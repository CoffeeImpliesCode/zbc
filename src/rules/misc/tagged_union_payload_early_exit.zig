//! Tagged-union payload early-exit detector.  An assignment
//!   `<path> = .{ .<Tag> = <expr> };`
//! where `<expr>` contains a `try` causes the union tag to be written to the
//! result location BEFORE the payload expression is evaluated.  If the
//! payload expression exits early via `try`, the LHS is left with the
//! new tag but the payload bytes from the PREVIOUS variant — garbage
//! state that later code (including errdefer cleanups) may misinterpret.
//!
//! Reported only when the target's storage is reachable from outside the
//! frame before the `try` runs — see `assignmentIsObservable`.  Real-world:
//! oven-sh/bun#29422.
//!
//! Fix: hoist the fallible expression into a `const` before the literal:
//!   const val = try computeErr();
//!   resolve.value = .{ .err = val };

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const file_model = @import("../../model/file_model.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const method_names = @import("../../model/method_names.zig");
const std_type_query = @import("../../model/std_type_query.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const R = "tagged-union-payload-early-exit";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .tagged_union_payload_early_exit)) return;
    const model = try cache.fileModel();

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        try checkBody(gpa, tree, cache, model, entry.proto, entry.body, problems);
    }
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    const binding_view = (try cache.localBindings(proto, body)).*;
    const bindings = &binding_view;

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // RHS must start with `= .{ .<Tag> =`
        if (tags[t] != .equal) continue;
        if (t + 4 > last) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .l_brace) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;

        // Must be a SINGLE-field literal (tagged union variant, not a plain struct).
        if (literalHasTopLevelComma(tags, t + 1, last)) continue;

        // Verify the `=` is an assignment to an existing location, not a
        // `const`/`var` declaration.  Walk back from t-1 across the LHS path.
        if (t == 0) continue;
        var lhs_end: Ast.TokenIndex = t;
        lhs_end -= 1;
        if (tags[lhs_end] != .identifier) continue;
        var lhs_start: Ast.TokenIndex = lhs_end;
        while (lhs_start >= 2 and tags[lhs_start - 1] == .period and tags[lhs_start - 2] == .identifier) {
            lhs_start -= 2;
        }
        // The token before the LHS path must be a statement boundary.
        if (lhs_start > first) {
            const prev = tags[lhs_start - 1];
            const ok = prev == .semicolon or prev == .l_brace or
                prev == .r_brace or prev == .keyword_return or
                prev == .equal_angle_bracket_right or prev == .pipe;
            if (!ok) continue;
        }

        // The target must resolve to a tagged union.  A known struct or
        // untagged union is not this rule's bug class; unknown types remain
        // conservative and continue to the diagnostic.
        const target_kind = try targetKind(tree, cache, model, bindings, lhs_start, lhs_end, t);
        if (target_kind == .not_tagged_union) continue;
        const rbrace = matchBrace(tags, t + 2, last) orelse continue;
        if (target_kind == .tagged_union and
            !try assignmentIsObservable(tree, cache, tags, bindings, first, last, t, lhs_start, rbrace))
            continue;

        // Scan inside `.{ ... }` for `keyword_try`; fire at the first one.
        var u: Ast.TokenIndex = t + 3;
        while (u < rbrace) : (u += 1) {
            if (tags[u] == .keyword_try) {
                try report(gpa, problems, tree, u);
                break;
            }
        }
        t = rbrace;
    }
}

/// True iff the anonymous literal at `period_tok` (`.` followed by `{`)
/// has MORE THAN ONE top-level field — `.{ .a = …, .b = … }`.
fn literalHasTopLevelComma(
    tags: []const std.zig.Token.Tag,
    period_tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (period_tok + 1 > last) return false;
    if (tags[period_tok + 1] != .l_brace) return false;
    const rbrace = matchBrace(tags, period_tok + 1, last) orelse return false;
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var fields: u32 = 0;
    var t: Ast.TokenIndex = period_tok + 2;
    while (t + 2 < rbrace) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            },
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .period => if (paren == 0 and brace == 0 and bracket == 0) {
                if (tags[t + 1] == .identifier and tags[t + 2] == .equal) {
                    fields += 1;
                    if (fields > 1) return true;
                }
            },
            else => {},
        }
    }
    return false;
}

const TargetKind = enum {
    tagged_union,
    not_tagged_union,
    unknown,
};

const TypeRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// The storage a `.loop_capture` iterates, when that storage is
/// nameable.
///
/// A name or a slice range over that name retains the storage declaration:
/// `fields` and `fields[0..n]` both name `fields`. A field path, call, or
/// pointer-to-array expression remains unresolved. Unknown storage does not
/// prove privacy.
///
/// The span is only the iterable for a `for` header.  `while` and
/// `if` record their condition in the same field, and a capture over
/// one of those is an immutable copy, not storage this rule places.
fn captureIterableName(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    capture: *const local_bindings.Binding,
) ?[]const u8 {
    if (capture.origin != .loop_capture) return null;
    if (capture.rhs_first < 2) return null;
    if (tags[capture.rhs_first - 2] != .keyword_for) return null;
    if (tags[capture.rhs_first] != .identifier) return null;
    if (capture.rhs_first != capture.rhs_last) {
        const open = capture.rhs_first + 1;
        if (tags[open] != .l_bracket) return null;
        if ((tokens.matchBracket(tags, open, capture.rhs_last) orelse return null) != capture.rhs_last)
            return null;
        var range_seen = false;
        for (tags[open + 1 .. capture.rhs_last]) |tag| {
            if (tag == .ellipsis2) range_seen = true;
        }
        if (!range_seen) return null;
    }
    return tree.tokenSlice(capture.rhs_first);
}

/// Element type of the storage a capture iterates — the type `field`
/// has inside `for (fields) |*field|`.
///
/// Proved from the storage binding: its own annotation
/// (`var fields: []Field = …`), the type argument of the allocation
/// that produced it (`allocator.alloc(Field, n)`), or an alias of one
/// of those.  A slice built by an expression the rule cannot read a
/// type out of stays unresolved, and an unresolved target reports.
fn captureElementTypeName(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    capture: *const local_bindings.Binding,
) ?[]const u8 {
    const iterable = captureIterableName(tree, tags, capture) orelse return null;
    const storage = bindings.findAt(iterable, capture.rhs_first) orelse return null;
    return storageElementTypeName(tree, tags, bindings, storage, 0);
}

fn storageElementTypeName(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    storage: *const local_bindings.Binding,
    depth: u8,
) ?[]const u8 {
    if (depth >= 8) return null;
    if (storage.origin == .param) {
        // A parameter's whole type expression is the annotation.
        return sliceElementTypeName(tree, tags, .{
            .first = storage.rhs_first,
            .last = storage.rhs_last,
        });
    }
    if (explicitTypeRange(tree, tags, storage)) |range| {
        if (sliceElementTypeName(tree, tags, range)) |name| return name;
    }
    if (storage.asCall()) |call| {
        // A chained call's element type lives behind the outermost
        // paren, which `CallInfo.paren_token` does not name.
        if (call.isChained()) return null;
        const method = call.method orelse return null;
        if (!isElementTypedAllocMethod(method)) return null;
        return allocCallTypeArgument(tree, tags, storage.rhs_last, call.paren_token);
    }
    return switch (storage.origin) {
        .alias => |source| blk: {
            const source_binding = bindings.findAt(source, storage.rhs_first) orelse
                break :blk null;
            break :blk storageElementTypeName(tree, tags, bindings, source_binding, depth + 1);
        },
        else => null,
    };
}

/// Allocation calls whose FIRST argument is the element type.
///
/// `isAllocMethodName` is deliberately broader — `realloc`,
/// `allocPrint` and `allocAdvanced` allocate too, but their first
/// argument is a buffer or a format string, and reading it as an
/// element type would name a type the call never returns.
fn isElementTypedAllocMethod(name: []const u8) bool {
    if (!method_names.isAllocMethodName(name)) return false;
    return std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "allocSentinel") or
        std.mem.eql(u8, name, "create") or
        std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "dupeZ");
}

/// The type argument of `allocator.alloc(<T>, n)` — the first
/// argument, and only when it is exactly one identifier.  A computed
/// element type (`alloc(@sizeOf(T), n)`) or a nested slice is left
/// unresolved rather than guessed at.
fn allocCallTypeArgument(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    rhs_last: Ast.TokenIndex,
    paren_token: Ast.TokenIndex,
) ?[]const u8 {
    const first = paren_token + 1;
    if (first > rhs_last or tags[first] != .identifier) return null;
    if (first + 1 <= rhs_last and tags[first + 1] != .comma and tags[first + 1] != .r_paren)
        return null;
    return tree.tokenSlice(first);
}

/// Element type of an array or slice type: `[]Field`, `[]const
/// Field`, `[:0]Field` and `[3]Field` all name `Field`.  An array of
/// arrays, or any other composite, is not named and the caller
/// reports.
fn sliceElementTypeName(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    range: TypeRange,
) ?[]const u8 {
    if (range.first > range.last or tags[range.first] != .l_bracket) return null;
    const close = tokens.matchBracket(tags, range.first, range.last) orelse return null;
    var first = close + 1;
    if (first > range.last) return null;
    if (tags[first] == .keyword_const) {
        first += 1;
        if (first > range.last) return null;
    }
    if (tags[first] != .identifier or first != range.last) return null;
    return tree.tokenSlice(first);
}

fn explicitTypeRange(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    binding: *const local_bindings.Binding,
) ?TypeRange {
    if (binding.name_token >= binding.rhs_first) return null;
    var t = binding.name_token + 1;
    while (t < binding.rhs_first) : (t += 1) {
        if (tags[t] != .colon) continue;
        if (t + 2 >= binding.rhs_first or tags[binding.rhs_first - 1] != .equal) return null;
        return .{ .first = t + 1, .last = binding.rhs_first - 2 };
    }
    _ = tree;
    return null;
}

fn bindingTypeRange(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    depth: u8,
) ?TypeRange {
    if (depth >= 8) return null;
    if (binding.origin == .param) {
        return .{ .first = binding.rhs_first, .last = binding.rhs_last };
    }
    if (explicitTypeRange(tree, tags, binding)) |range| return range;
    return switch (binding.origin) {
        .alias => |source| blk: {
            const source_binding = bindings.findAt(source, binding.rhs_first) orelse
                break :blk null;
            break :blk bindingTypeRange(tree, tags, bindings, source_binding, depth + 1);
        },
        else => null,
    };
}

fn terminalTypeName(tree: *const Ast, range: TypeRange) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    var last: ?Ast.TokenIndex = null;
    var t = range.first;
    while (t <= range.last) : (t += 1) {
        if (tags[t] == .identifier) last = t;
    }
    return if (last) |tok| tree.tokenSlice(tok) else null;
}

fn targetKind(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    bindings: *const local_bindings.LocalBindings,
    lhs_start: Ast.TokenIndex,
    lhs_end: Ast.TokenIndex,
    use_tok: Ast.TokenIndex,
) !TargetKind {
    // Resolve the complete LHS in its actual declaration context. In
    // particular, `?Reader` is an optional STRUCT, not a tagged union
    // merely because its assignment uses a one-field literal.
    if (cache.zls) |resolver| {
        if (cache.nodeForExactSpan(lhs_start, lhs_end)) |node| {
            var actual = (try resolver.resolutionFrame().typeOfNode(node)) orelse return .unknown;
            while (resolver.typeTag(actual) == .optional)
                actual = (try resolver.normalizedType(resolver.childType(actual) orelse return .unknown)) orelse return .unknown;
            switch (resolver.typeTag(actual) orelse return .unknown) {
                .@"union" => {
                    const container = switch (actual.data) {
                        .container => |container| container,
                        else => return .unknown,
                    };
                    const owner_tree = &container.scope_handle.handle.document.tree;
                    const union_token = owner_tree.nodeMainToken(container.scope_handle.toNode());
                    const owner_tags = owner_tree.tokens.items(.tag);
                    if (owner_tags[union_token] != .keyword_union or union_token + 1 >= owner_tags.len)
                        return .unknown;
                    return if (owner_tags[union_token + 1] == .l_paren) .tagged_union else .not_tagged_union;
                },
                .@"struct", .@"enum", .int, .float, .pointer => return .not_tagged_union,
                else => return .unknown,
            }
        }
    }
    const tags = tree.tokens.items(.tag);
    const root_name = tree.tokenSlice(lhs_start);
    const binding = bindings.findAt(root_name, use_tok) orelse return .unknown;
    var type_info = rootTypeInfo(tree, model, bindings, binding) orelse return .unknown;

    var field_tok = lhs_start + 1;
    while (field_tok < lhs_end) : (field_tok += 2) {
        if (field_tok + 1 > lhs_end or tags[field_tok] != .period or
            tags[field_tok + 1] != .identifier)
            return .unknown;
        type_info = model.resolveFieldTypeQualifiedTi(
            type_info,
            tree.tokenSlice(field_tok + 1),
        ) orelse return .unknown;
    }
    if (type_info.kind != .union_) return .not_tagged_union;
    return if (typeInfoIsTaggedUnion(model, type_info)) .tagged_union else .not_tagged_union;
}

/// The type the ROOT of the assignment path denotes.
///
/// For a declaration that is its own type; for a loop capture it is
/// the ELEMENT type of the storage the capture iterates, because
/// `field.kind` selects on `Field`, not on `field`.
fn rootTypeInfo(
    tree: *const Ast,
    model: *const file_model.FileModel,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
) ?*const file_model.TypeInfo {
    const tags = tree.tokens.items(.tag);
    if (binding.origin == .loop_capture) {
        const elem = captureElementTypeName(tree, tags, bindings, binding) orelse return null;
        return model.findType(elem);
    }
    const range = bindingTypeRange(tree, tags, bindings, binding, 0) orelse return null;
    const type_name = terminalTypeName(tree, range) orelse return null;
    return model.findType(type_name);
}

fn typeInfoIsTaggedUnion(
    model: *const file_model.FileModel,
    type_info: *const file_model.TypeInfo,
) bool {
    const tags = model.tree.tokens.items(.tag);
    var union_tok = type_info.body_first;
    while (union_tok > 0 and tags[union_tok] != .keyword_union) : (union_tok -= 1) {}
    if (union_tok + 2 >= model.tree.tokens.len or tags[union_tok + 1] != .l_paren)
        return false;
    var depth: u32 = 1;
    var t = union_tok + 2;
    while (t < model.tree.tokens.len and depth > 0) : (t += 1) {
        if (tags[t] == .l_paren) depth += 1 else if (tags[t] == .r_paren) depth -= 1;
    }
    return depth == 0 and t > union_tok + 3;
}

fn typeRangeStartsPointer(tree: *const Ast, range: TypeRange) bool {
    const tags = tree.tokens.items(.tag);
    var t = range.first;
    while (t <= range.last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => {},
            .asterisk => return true,
            else => return false,
        }
    }
    return false;
}

/// True when a half-retagged union written at `assignment_tok` can still
/// be read by anything that outlives the `try` skipping its payload.
///
/// A loop capture writes THROUGH the storage it iterates, so what needs
/// proving is the storage's privacy — but privacy is necessary, not
/// sufficient, and that branch runs the escape and publication proofs a
/// plain root gets instead of returning on the storage proof alone.  The
/// capture is a pointer to the very element the retag corrupts, so
/// handing IT to a callee publishes the union exactly as handing the
/// slice does, and a `&storage` taken before the write publishes it for
/// the same reason.
fn assignmentIsObservable(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    lhs_start: Ast.TokenIndex,
    literal_end: Ast.TokenIndex,
) !bool {
    const root_name = tree.tokenSlice(lhs_start);
    const binding = bindings.findAt(root_name, assignment_tok) orelse return true;
    if (binding.origin == .param) return true;
    if (!try targetPathIsInline(tree, cache, bindings, binding, lhs_start, assignment_tok - 1))
        return true;
    if (binding.origin == .loop_capture) {
        if (!try captureStorageIsFramePrivate(
            tree,
            cache,
            tags,
            bindings,
            body_first,
            body_last,
            assignment_tok,
            binding,
            if (lhs_start + 2 < assignment_tok) tree.tokenSlice(lhs_start + 2) else null,
        )) return true;
        if (captureReachesOutsideFrame(tree, tags, bindings, body_first, literal_end, binding))
            return true;
        const storage_name = captureIterableName(tree, tags, binding) orelse return true;
        if (hasEscapedAddressAlias(
            tree,
            tags,
            bindings,
            body_first,
            body_last,
            literal_end,
            storage_name,
        )) return true;
        return hasPreCommitPublication(
            tree,
            tags,
            bindings,
            body_first,
            body_last,
            literal_end,
            storage_name,
        );
    }
    // Annotation spellings can themselves alias pointers. Use the actual
    // root type when available, including inferred call/orelse initializers.
    if (cache.zls) |resolver| {
        const node = cache.nodeForExactSpan(lhs_start, lhs_start) orelse return true;
        const actual = (try resolver.resolutionFrame().typeOfNode(node)) orelse return true;
        switch (resolver.typeTag(actual) orelse return true) {
            .@"struct", .@"union" => {},
            else => return true,
        }
    } else {
        const model = try cache.fileModel();
        const root = rootTypeInfo(tree, model, bindings, binding) orelse return true;
        if (root.kind != .struct_ and root.kind != .union_) return true;
        const range = bindingTypeRange(tree, tags, bindings, binding, 0) orelse return true;
        if (typeRangeStartsPointer(tree, range)) return true;
    }
    if (hasDeferredObserver(tree, tags, body_first, body_last, assignment_tok, root_name))
        return true;
    if (hasEscapedAddressAlias(
        tree,
        tags,
        bindings,
        body_first,
        body_last,
        literal_end,
        root_name,
    )) return true;
    return hasPreCommitPublication(
        tree,
        tags,
        bindings,
        body_first,
        body_last,
        literal_end,
        root_name,
    );
}

/// A private header does not own a pointee reached through one of its fields.
/// Every intermediate projection must stay in inline aggregate storage.
fn targetPathIsInline(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) !bool {
    if (first + 2 >= last) return true;
    if (cache.zls) |resolver| {
        var end = first + 2;
        while (end < last) : (end += 2) {
            const node = cache.nodeForExactSpan(first, end) orelse return false;
            const actual = (try resolver.resolutionFrame().typeOfNode(node)) orelse return false;
            switch (resolver.typeTag(actual) orelse return false) {
                .@"struct", .@"union" => {},
                else => return false,
            }
        }
        return true;
    }
    const model = try cache.fileModel();
    var owner = rootTypeInfo(tree, model, bindings, binding) orelse return false;
    var field = first + 2;
    while (field < last) : (field += 2) {
        const declaration = owner.findField(tree.tokenSlice(field)) orelse return false;
        if (typeRangeStartsPointer(tree, .{ .first = declaration.type_first, .last = declaration.type_last }))
            return false;
        owner = model.resolveFieldTypeQualifiedTi(owner, tree.tokenSlice(field)) orelse return false;
        if (owner.kind != .struct_ and owner.kind != .union_) return false;
    }
    return true;
}

/// True when the union element a loop capture writes through lives in
/// storage this frame allocated, releases raw on the failing path,
/// and has published nothing before the write.
///
/// `for (fields) |*field| { field.kind = .{ … try … } }` writes into
/// `fields`'s storage, and the half-retagged element is observable
/// only if something can still read it after the tag flips: a caller
/// that owns the slice, a cleanup registered before the write, or
/// anything the frame handed the slice to.  A fresh allocation the
/// frame releases raw (`errdefer … allocator.free(fields)`) reaches
/// nobody — the release hands the bytes back without interpreting
/// them — which is ocean's `decodeModuleLayouts`, where the layout
/// carrying `fields` is published only after the loop finishes.
///
/// Every step is a proof, and an unproved step reports:
///
///   - the iterable names storage this frame owns (never a
///     parameter) whose element type resolves, so the write is known
///     to land in a slice rather than in something unplaced;
///   - a `defer` / `errdefer` before the assignment DOMINATES the
///     write — its block is an ancestor of the block the write is
///     written in, and it is registered unconditionally — and that
///     cleanup raw-frees the exact allocation through its own allocator,
///     or releases its proved private standard arena;
///   - no cleanup reads the retagged field. An exact loop capture can read
///     another declared field without observing the union. A cleanup that
///     releases raw and also reads the union remains an observer.
///   - every other mention of that storage before the assignment is
///     its own declaration, a proved allocation, an element write, or a loop header.
///     Anything else could have published the slice.
fn captureStorageIsFramePrivate(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    capture: *const local_bindings.Binding,
    target_field: ?[]const u8,
) !bool {
    const iterable = captureIterableName(tree, tags, capture) orelse return false;
    const storage = bindings.findAt(iterable, capture.rhs_first) orelse return false;
    // The caller owns a parameter's slice and reads it on the error
    // path, even when the frame frees it afterwards.
    if (storage.origin == .param) return false;
    const element_name = storageElementTypeName(tree, tags, bindings, storage, 0) orelse return false;
    const element = if (cache.zls != null)
        (try actualCaptureElement(cache, capture.rhs_first)) orelse return false
    else
        (try cache.fileModel()).findType(element_name) orelse return false;
    const allocation = privateStorageAllocation(tree, cache, tags, bindings, storage, assignment_tok) orelse return false;

    var raw_free_seen = false;
    if (allocation.arena) |arena| {
        raw_free_seen = arenaReleasedBeforeWrite(tree, tags, bindings, body_first, body_last, assignment_tok, arena);
        if (!raw_free_seen) return false;
    }
    var t = body_first;
    while (t < assignment_tok) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, body_last);
            continue;
        }
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            const end = tokens.skipDeferStmt(tags, t, body_last) orelse return false;
            switch (classifyCleanup(tree, cache, tags, bindings, t, end, iterable, capture.name, element, target_field, allocation.allocator)) {
                // A cleanup that reads what the retag corrupted settles
                // it, whether or not it also releases raw.
                .observes => return false,
                .releases_raw => {
                    if (end < assignment_tok and
                        deferDominatesWrite(tags, body_first, body_last, assignment_tok, t))
                    {
                        raw_free_seen = true;
                    }
                },
                .ignores_storage => {},
            }
            t = end;
            continue;
        }
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), iterable)) continue;
        if (t == storage.name_token) continue;
        if (isLoopIterableToken(tree, tags, bindings, t)) continue;
        // `fields = allocator.alloc(…)` rebinds the name to a new
        // allocation; the frame still owns it, and the release that
        // follows it is what the privacy proof rests on.
        if (t + 1 < assignment_tok and tags[t + 1] == .equal) continue;
        // Initializing an element writes private storage, not a copy of
        // its address to another owner.  Keep scanning the index and RHS:
        // either can contain a separate mention that publishes the slice.
        if (isIndexedStorageWrite(tags, t, assignment_tok - 1)) continue;
        return false;
    }
    return raw_free_seen;
}

/// The slice's actual element declaration owns its field names. This follows
/// module aliases in the existing resolution frame, never by a leaf-name search.
fn actualCaptureElement(
    cache: *file_cache_mod.FileCache,
    storage_token: Ast.TokenIndex,
) !?*const file_model.TypeInfo {
    const resolver = cache.zls orelse return null;
    const node = cache.nodeForExactSpan(storage_token, storage_token) orelse return null;
    const slice = (try resolver.resolutionFrame().typeOfNode(node)) orelse return null;
    if (resolver.pointerSize(slice) != .slice) return null;
    const element = (try resolver.normalizedType(resolver.childType(slice) orelse return null)) orelse return null;
    const container = switch (element.data) {
        .container => |container| container,
        else => return null,
    };
    const handle = container.scope_handle.handle;
    const owner_tree = &handle.document.tree;
    const owner_cache = if (owner_tree == cache.tree)
        cache
    else
        &(try cache.sourceDocument(handle)).cache;
    const model = try owner_cache.fileModel();
    for (model.types) |*candidate| {
        if (container.scope_handle.scope == .root) {
            if (candidate.body_first == 0) return candidate;
        } else if (candidate.body_last == owner_tree.lastToken(container.scope_handle.toNode())) {
            return candidate;
        }
    }
    return null;
}

const PrivateAllocation = struct {
    arena: ?*const local_bindings.Binding = null,
    allocator: ?*const local_bindings.Binding = null,
};

/// Every generation of the slice must come from an exact allocator call.
/// An annotation or a free of a copied caller header does not prove ownership.
fn privateStorageAllocation(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    storage: *const local_bindings.Binding,
    before: Ast.TokenIndex,
) ?PrivateAllocation {
    var allocation = privateAllocationExpression(tree, cache, tags, bindings, storage.rhs_first, storage.rhs_last);
    if (allocation == null and !emptySliceInitializer(tags, storage.rhs_first, storage.rhs_last)) return null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .assign) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const pair = tree.nodeData(node).node_and_node;
        const lhs = pair[0];
        const tok = tree.firstToken(lhs);
        if (tok <= storage.name_token or tok >= before or tree.nodeTag(lhs) != .identifier) continue;
        if (bindings.findAt(tree.tokenSlice(tok), tok) != storage) continue;
        const next = privateAllocationExpression(tree, cache, tags, bindings, tree.firstToken(pair[1]), tree.lastToken(pair[1])) orelse return null;
        if (allocation) |previous| {
            if (previous.arena != next.arena or previous.allocator != next.allocator) return null;
        }
        allocation = next;
    }
    return allocation;
}

fn emptySliceInitializer(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    return last == first + 3 and tags[first] == .ampersand and
        tags[first + 1] == .period and tags[first + 2] == .l_brace and tags[last] == .r_brace;
}

fn privateAllocationExpression(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?PrivateAllocation {
    var start = first;
    if (tags[start] == .keyword_try) start += 1;
    if (start + 3 > last or tags[start] != .identifier or tags[start + 1] != .period or
        tags[start + 2] != .identifier or tags[start + 3] != .l_paren) return null;
    if (!isElementTypedAllocMethod(tree.tokenSlice(start + 2))) return null;
    const close = tokens.matchParen(tags, start + 3, last) orelse return null;
    if (close != last and !(close + 2 <= last and tags[close + 1] == .keyword_catch and tags[close + 2] == .keyword_return))
        return null;
    if (receiverIsStandardAllocator(cache, tree, tags, bindings, start)) {
        const owner = allocatorBinding(bindings, tree.tokenSlice(start), start, 0) orelse return null;
        const range = bindingTypeRange(tree, tags, bindings, owner, 0) orelse return null;
        if (typeRangeStartsPointer(tree, range)) return null;
        return .{ .allocator = owner };
    }
    const allocator = bindings.findAt(tree.tokenSlice(start), start) orelse return null;
    const call = allocator.asCall() orelse return null;
    if (call.isChained() or !std.mem.eql(u8, call.method orelse return null, "allocator")) return null;
    const arena = bindings.findAt(call.receiver, call.receiver_token) orelse return null;
    const arena_first = arena.rhsFirstAfterTry(tags);
    var paren = arena_first;
    while (paren <= arena.rhs_last and tags[paren] != .l_paren) : (paren += 1) {}
    if (paren < arena_first + 3 or paren > arena.rhs_last or
        tags[paren - 2] != .period or !std.mem.eql(u8, tree.tokenSlice(paren - 1), "init")) return null;
    if (!std_type_query.isType(cache, tree, arena_first, paren - 3, "heap", "ArenaAllocator", .{})) return null;
    return .{ .arena = arena };
}

fn allocatorBinding(
    bindings: *const local_bindings.LocalBindings,
    name: []const u8,
    use: Ast.TokenIndex,
    depth: u8,
) ?*const local_bindings.Binding {
    if (depth >= 8) return null;
    const binding = bindings.findAt(name, use) orelse return null;
    if (!binding.is_const) return null;
    return switch (binding.origin) {
        .alias => |source| allocatorBinding(bindings, source, binding.rhs_first, depth + 1),
        else => binding,
    };
}

fn arenaReleasedBeforeWrite(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    before: Ast.TokenIndex,
    arena: *const local_bindings.Binding,
) bool {
    var release_seen = false;
    var t = arena.name_token + 1;
    while (t < before) : (t += 1) {
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            const end = tokens.skipDeferStmt(tags, t, last) orelse return false;
            if (t + 6 == end and tags[t + 1] == .identifier and
                bindings.findAt(tree.tokenSlice(t + 1), t + 1) == arena and
                tags[t + 2] == .period and std.mem.eql(u8, tree.tokenSlice(t + 3), "deinit") and
                tags[t + 4] == .l_paren and tags[t + 5] == .r_paren and
                deferDominatesWrite(tags, first, last, before, t))
            {
                release_seen = true;
                t = end;
                continue;
            }
        }
        if (tags[t] != .identifier or bindings.findAt(tree.tokenSlice(t), t) != arena) continue;
        if (t + 4 < before and tags[t + 1] == .period and
            std.mem.eql(u8, tree.tokenSlice(t + 2), "allocator") and
            tags[t + 3] == .l_paren and tags[t + 4] == .r_paren) continue;
        return false;
    }
    return release_seen;
}

fn disjointCaptureRead(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
    element: *const file_model.TypeInfo,
    target: []const u8,
) bool {
    if (tok + 2 > last or tags[tok + 1] != .period or tags[tok + 2] != .identifier) return false;
    if (tok > 0 and tags[tok - 1] == .ampersand) return false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .address_of) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) <= tok and tree.lastToken(node) >= tok) return false;
    }
    var tail = tok;
    while (tail + 2 <= last and tags[tail + 1] == .period and tags[tail + 2] == .identifier)
        tail += 2;
    if (tail < last and tags[tail + 1] == .l_paren) return false;
    const field = tree.tokenSlice(tok + 2);
    return !std.mem.eql(u8, field, target) and element.findField(field) != null;
}

/// A cleanup may read another declared field without interpreting the union.
/// The whole loop is checked, including every use of its exact capture.
fn cleanupReadsDisjointField(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    use: Ast.TokenIndex,
    storage_name: []const u8,
    element: *const file_model.TypeInfo,
    target_field: ?[]const u8,
) bool {
    const target = target_field orelse return false;
    if (bindings.findAt(tree.tokenSlice(use), use)) |capture| {
        if (captureIterableName(tree, tags, capture)) |iterable| {
            // findAt includes the declaration token. Only a value use takes
            // this path; the binder must pass the whole-loop check below.
            if (use != capture.name_token and std.mem.eql(u8, iterable, storage_name))
                return disjointCaptureRead(tree, tags, use, last, element, target);
        }
    }
    for (bindings.items) |*capture| {
        if (capture.name_token < first or capture.name_token > last) continue;
        // The capture declaration names the binding, not the element value.
        // Certify its uses with the same whole-loop check as the iterable.
        if (capture.rhs_first != use and capture.name_token != use) continue;
        const iterable = captureIterableName(tree, tags, capture) orelse continue;
        if (!std.mem.eql(u8, iterable, storage_name)) continue;
        var t = capture.name_token + 1;
        while (t <= @min(last, capture.scope_close)) : (t += 1) {
            if (tags[t] != .identifier or bindings.findAt(tree.tokenSlice(t), t) != capture) continue;
            if (t > 0 and tags[t - 1] == .period) continue;
            if (!disjointCaptureRead(tree, tags, t, last, element, target)) return false;
        }
        return true;
    }
    return false;
}

/// True only for the root of `storage[index] = …`, not an indexed read
/// passed to a callee or copied elsewhere.  The caller still scans every
/// token inside the index and the initializer.
fn isIndexedStorageWrite(
    tags: []const std.zig.Token.Tag,
    root: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (root + 1 > last or tags[root + 1] != .l_bracket) return false;
    const close = tokens.matchBracket(tags, root + 1, last) orelse return false;
    return close < last and tags[close + 1] == .equal;
}

/// True when a call argument contains the capture itself — a pointer to
/// the element the retag corrupts — before the write.
///
/// A plain read through the capture (`if (field.kind == .ordinary)`)
/// and a write through it (`field.byte_offset = …`) both stay inside
/// the loop body and publish nothing.  One shape does publish: the
/// capture, or a path through it, sitting in a call's argument list —
/// `observe(field)`, `log(field.kind)`, `&field` — because each hands
/// the callee a route to the element that is still live when the
/// `try` unwinds.
fn captureReachesOutsideFrame(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    capture: *const local_bindings.Binding,
) bool {
    const storage_name = captureIterableName(tree, tags, capture) orelse return true;
    var use = capture.name_token + 1;
    while (use < @min(assignment_tok, capture.scope_close)) : (use += 1) {
        if (tags[use] == .keyword_fn) {
            use = skipNestedFn(tags, use, assignment_tok);
            continue;
        }
        if (tags[use] != .identifier or (use > 0 and tags[use - 1] == .period)) continue;
        if (bindings.findAt(tree.tokenSlice(use), use) == capture) {
            if (use + 2 < assignment_tok and tags[use + 1] == .period) {
                if (tags[use + 2] == .asterisk and use + 3 < assignment_tok and tags[use + 3] == .equal)
                    continue;
                if (tags[use + 2] == .identifier) {
                    var tail = use + 2;
                    while (tail + 2 < assignment_tok and tags[tail + 1] == .period and tags[tail + 2] == .identifier)
                        tail += 2;
                    if (tail + 1 >= assignment_tok or tags[tail + 1] != .l_paren) continue;
                }
            }
            return true;
        }
        if (!std.mem.eql(u8, tree.tokenSlice(use), storage_name)) continue;
        if (readsElementCountOnly(tree, tags, use) or isLoopIterableToken(tree, tags, bindings, use)) continue;
        if (isIndexedStorageWrite(tags, use, assignment_tok - 1)) continue;
        return true;
    }
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .address_of) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const amp = tree.firstToken(node);
        if (amp <= capture.name_token or amp >= assignment_tok) continue;
        const root = addressOperandRoot(tree, tree.nodeData(node).node);
        if (tree.nodeTag(root) != .identifier) continue;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        if (std.mem.eql(u8, name, capture.name) or std.mem.eql(u8, name, storage_name)) return true;
    }
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const paren = tree.nodeMainToken(node);
        if (paren < body_first or paren >= assignment_tok) continue;
        if (insideNestedFn(tags, body_first, assignment_tok, paren)) continue;
        var call_buf: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buf, node) orelse continue;
        for (call.ast.params) |arg| {
            const first = tree.firstToken(arg);
            const last = @min(tree.lastToken(arg), assignment_tok - 1);
            var t = @max(first, capture.name_token + 1);
            while (t <= last and t < capture.scope_close) : (t += 1) {
                if (tags[t] == .keyword_fn) {
                    t = skipNestedFn(tags, t, last);
                    continue;
                }
                if (tags[t] == .identifier and
                    (std.mem.eql(u8, tree.tokenSlice(t), capture.name) or
                        std.mem.eql(u8, tree.tokenSlice(t), storage_name)) and
                    t > 0 and tags[t - 1] != .period)
                {
                    return true;
                }
            }
        }
    }
    return false;
}

/// What one `defer` / `errdefer` statement does to the storage a
/// capture writes through.
const CleanupVerdict = enum {
    /// It never names the storage or the captured element.
    ignores_storage,
    /// Its only route to the storage is a `free` that resolves to the
    /// standard allocator: the bytes go back without being read.
    releases_raw,
    /// It names the storage or the captured element some other way, so
    /// it can dispatch on — or copy out of — the union the retag
    /// flipped.
    observes,
};

/// Classify one cleanup statement by EVERY route it takes to the
/// storage, not by the first route that matches.  `errdefer { gpa.free
/// (fields); trace(fields[0].kind); }` releases raw AND reads, and the
/// read is the half that decides observability: the release hands the
/// bytes back, and what runs after it still interprets them.  The
/// release argument is the one span where naming the storage is
/// expected, so the scan steps over the whole resolved call.
///
/// `fields.len` cannot reach an element — a length is not the union and
/// the retag did not change it — so the guard ocean writes around its
/// release (`errdefer if (fields.len != 0) allocator.free(fields);`) is
/// not an observation.  That `if` guards WHICH release runs; the
/// `errdefer` itself is registered unconditionally, and when the guard
/// is false the storage is the empty `&.{}` its declaration gave it, so
/// there was nothing to release.
fn classifyCleanup(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    kw: Ast.TokenIndex,
    end: Ast.TokenIndex,
    storage_name: []const u8,
    capture_name: []const u8,
    element: *const file_model.TypeInfo,
    target_field: ?[]const u8,
    allocator: ?*const local_bindings.Binding,
) CleanupVerdict {
    var releases_raw = false;
    var observes = false;
    var t = kw;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (isResolvedAllocatorFree(tree, cache, tags, bindings, t, end)) |close| {
            // Only the exact storage argument is a raw release. Naming
            // `storage.len` inside some other allocation's argument is not.
            if (t + 3 == close and tags[t + 2] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t + 2), storage_name) and allocator != null and
                allocatorBinding(bindings, tree.tokenSlice(t - 2), t - 2, 0) == allocator)
            {
                releases_raw = true;
                t = close;
                continue;
            }
        }
        const text = tree.tokenSlice(t);
        if (!std.mem.eql(u8, text, storage_name) and !std.mem.eql(u8, text, capture_name)) continue;
        if (readsElementCountOnly(tree, tags, t)) continue;
        if (cleanupReadsDisjointField(tree, tags, bindings, kw, end, t, storage_name, element, target_field))
            continue;
        observes = true;
        break;
    }
    if (observes) return .observes;
    if (releases_raw) return .releases_raw;
    return .ignores_storage;
}

/// True when the name at `tok` is read only for a length or a capacity:
/// a scalar the retag did not change, and a route to no element.
fn readsElementCountOnly(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    tok: Ast.TokenIndex,
) bool {
    if (tok + 2 >= tags.len) return false;
    if (tags[tok + 1] != .period or tags[tok + 2] != .identifier) return false;
    const field = tree.tokenSlice(tok + 2);
    return std.mem.eql(u8, field, "len") or std.mem.eql(u8, field, "cap");
}

/// The `)` that closes a standard-allocator `free` written at `callee`,
/// or null when `callee` is not one.
///
/// A release counts as raw only when the RECEIVER's declared type
/// resolves to `std.mem.Allocator`, read through the scopes that type is
/// written in — so an alias of it counts and a look-alike does not.  A
/// `free` spelled as a bare call (`free(fields)`, a file-local `fn
/// free`), a method on any other type, and a receiver this walk cannot
/// place (`x.gpa.free(…)`, `arena.allocator().free(…)`) are all
/// refusals.  A refused release is never treated as evidence of privacy:
/// the argument the call was handed stays an ordinary read in the
/// cleanup that made it, so the cleanup observes and the rule reports.
fn isResolvedAllocatorFree(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    callee: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?Ast.TokenIndex {
    if (callee + 1 > end) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(callee), "free")) return null;
    if (tags[callee + 1] != .l_paren) return null;
    if (callee < 2 or tags[callee - 1] != .period or tags[callee - 2] != .identifier) return null;
    // `x.gpa.free(…)` — a field path is not the plain name whose
    // declared type this walk reads.
    if (callee >= 3 and tags[callee - 3] == .period) return null;
    if (!receiverIsStandardAllocator(cache, tree, tags, bindings, callee - 2)) return null;
    return tokens.matchParen(tags, callee + 1, end);
}

fn receiverIsStandardAllocator(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    recv: Ast.TokenIndex,
) bool {
    const recv_name = tree.tokenSlice(recv);
    const binding = bindings.findAt(recv_name, recv) orelse return false;
    const range = bindingTypeRange(tree, tags, bindings, binding, 0) orelse return false;
    return std_type_query.isType(cache, tree, range.first, range.last, "mem", "Allocator", .{
        .allow_pointer = true,
    });
}

/// True when a cleanup registered at `defer_tok` is both LIVE and ARMED
/// when the `try` inside the write at `assignment_tok` unwinds.
///
/// Two facts, and neither of them is a brace count:
///
///   - the block the cleanup is registered in must be the write's own
///     block or an ANCESTOR of it.  Depth cannot say this: a sibling
///     block and the write sit at the same depth, and the sibling's
///     scope has ended by the time the write runs, so nothing it
///     registered is left to run on the failing path.
///   - the registration must be reached on every path that reaches the
///     write.  Zig's grammar admits a `defer` / `errdefer` only as a
///     block item, never as the braceless body of an `if` / `else` /
///     `switch` prong, so a conditionally armed cleanup is always a
///     BRACED arm — and a braced arm that does not enclose the write is
///     refused by the block test above.  A braced arm that DOES enclose
///     the write is the only way to reach that write, so its cleanup is
///     armed whenever the write runs.  An `if` INSIDE the guarded
///     statement (`errdefer if (len != 0) free(…);`) guards which
///     release runs, not whether the errdefer is armed.
///
/// `try` propagates out of the function, so a cleanup in any block that
/// encloses the write is reached on the failing path; no exit-path
/// question beyond that one is left open.
fn deferDominatesWrite(
    tags: []const std.zig.Token.Tag,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    defer_tok: Ast.TokenIndex,
) bool {
    const release = enclosingBlock(tags, body_first, body_last, defer_tok) orelse return false;
    const write = enclosingBlock(tags, body_first, body_last, assignment_tok) orelse return false;
    return !(write.open < release.open or write.close > release.close);
}

const Block = struct { open: Ast.TokenIndex, close: Ast.TokenIndex };

/// The innermost `{ … }` pair written around `tok`, counting from the
/// body's own opening brace.  A nest deeper than the walk holds refuses
/// rather than answering with the wrong frame.
fn enclosingBlock(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    tok: Ast.TokenIndex,
) ?Block {
    var open_stack: [16]Ast.TokenIndex = undefined;
    var depth: usize = 0;
    var t = first;
    while (t < tok) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (depth == open_stack.len) return null;
                open_stack[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth == 0) return null;
                depth -= 1;
            },
            else => {},
        }
    }
    if (depth == 0) return null;
    const open = open_stack[depth - 1];
    const close = matchBrace(tags, open, last) orelse return null;
    return .{ .open = open, .close = close };
}


/// True when `tok` is the whole iterable of a `for` loop — the token
/// a capture's `rhs` span points at.  Those mentions ARE the loop,
/// so they publish nothing.
fn isLoopIterableToken(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    tok: Ast.TokenIndex,
) bool {
    for (bindings.items) |*binding| {
        if (binding.origin != .loop_capture) continue;
        if (binding.rhs_first == tok and captureIterableName(tree, tags, binding) != null) return true;
    }
    return false;
}

fn hasDeferredObserver(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    root_name: []const u8,
) bool {
    if (assignment_tok <= first) return false;
    var t = first;
    while (t < assignment_tok) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_defer and tags[t] != .keyword_errdefer) continue;
        const end = tokens.skipDeferStmt(tags, t, last) orelse return true;
        var u = t + 1;
        while (u <= end and u < assignment_tok) : (u += 1) {
            if (tags[u] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(u), root_name) and
                (u == 0 or tags[u - 1] != .period))
                return true;
        }
        t = end;
    }
    return false;
}

fn hasEscapedAddressAlias(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    root_name: []const u8,
) bool {
    for (bindings.items) |*binding| {
        if (binding.name_token >= assignment_tok) continue;
        if (!bindingAliasesRoot(bindings, binding, root_name, 0)) continue;
        if (addressAliasEscapes(tree, tags, first, last, binding.name, binding.name_token))
            return true;
    }
    return false;
}

/// True iff the root's address reaches a destination outside this frame
/// before the complete initializer commits.
///
/// `assignmentIsObservable` suppresses a by-value local whose union field
/// is written only inside the frame that owns it: on the error path that
/// frame dies with nothing able to read the half-retagged union.  That
/// proof holds only while the storage stays private, so the question is
/// never "was `&root` written down" — it is "where did it go".
///
/// An address reaches outside the frame when a callee receives it, when a
/// `defer`/`errdefer` or a `return` hands it on, or when it is stored into
/// storage the frame does not own (`registry.saved = &result`, where
/// `registry` is a parameter).  Observability is bounded by the frame: the
/// reader that matters is one running while this frame is still unwinding —
/// a callee entered before the `try`, or the frame's own cleanup — not a
/// use of the pointer after the frame's storage is gone.
///
/// The scan walks `address_of` NODES, not `&` tokens, so a binary
/// `bits & result.mask` is not an address expression and a grouped
/// `&(result)` still names the local.
fn hasPreCommitPublication(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    root_name: []const u8,
) bool {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .address_of) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const amp = tree.firstToken(node);
        if (amp < body_first or amp > body_last) continue;
        // The boundary includes the fallible payload. Publication after
        // the complete initializer cannot run on this error path.
        if (amp >= assignment_tok) continue;
        const operand = addressOperandToken(tree, tree.nodeData(node).node) orelse continue;
        if (tree.tokenTag(operand) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(operand), root_name)) continue;
        // A nested `fn` cannot capture a local of the enclosing frame, so
        // an `&root` inside one publishes nothing.
        if (insideNestedFn(tags, body_first, body_last, amp)) continue;
        if (addressReachesOutsideFrame(tree, tags, bindings, body_first, body_last, amp))
            return true;
    }
    return false;
}

/// Main token of an `&expr` operand, looking through the parentheses of a
/// grouped expression so `&(result)` names the same local as `&result`.
fn addressOperandToken(tree: *const Ast, node: Ast.Node.Index) ?Ast.TokenIndex {
    if (tree.nodeTag(node) == .grouped_expression) {
        return addressOperandToken(tree, tree.nodeData(node).node_and_token[0]);
    }
    return tree.nodeMainToken(node);
}

fn addressOperandRoot(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    return switch (tree.nodeTag(node)) {
        .grouped_expression, .field_access => addressOperandRoot(tree, tree.nodeData(node).node_and_token[0]),
        .array_access => addressOperandRoot(tree, tree.nodeData(node).node_and_node[0]),
        else => node,
    };
}

fn insideNestedFn(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    tok: Ast.TokenIndex,
) bool {
    var t = first;
    while (t < tok) : (t += 1) {
        if (tags[t] != .keyword_fn) continue;
        const end = skipNestedFn(tags, t, last);
        if (tok <= end) return true;
        t = end;
    }
    return false;
}

/// True when the `&root` at `amp` lands somewhere that outlives the frame's
/// own use of it.
///
/// Private destinations are exactly the ones that die with the frame:
///
///   - `_ = &root;` — the address is dropped outright;
///   - the initializer of a local declaration whose own name never escapes
///     (`const alias = &root; observe(alias);` publishes, and
///     `const alias = &root; _ = alias;` does not);
///   - a store into a frame-local that never escapes, aggregates included
///     (`const holder = Holder{ .spec = &root };` stays private until
///     `holder` itself is handed somewhere).
///
/// A call argument, a `defer`, a `return`, and a store into storage the
/// frame does not own all publish.
fn addressReachesOutsideFrame(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    amp: Ast.TokenIndex,
) bool {
    const head = statementHead(tags, body_first, amp);
    if (head + 1 > body_last) return true;
    switch (tags[head]) {
        .keyword_const, .keyword_var => {
            if (tags[head + 1] != .identifier) return true;
            return destinationEscapes(tree, tags, bindings, body_first, body_last, head + 1);
        },
        .identifier => {
            // `_ = &root;` — discarding the address reaches nobody.
            if (tags[head + 1] == .equal and
                std.mem.eql(u8, tree.tokenSlice(head), "_")) return false;
            // `local.saved = &root` — the destination is the path's root.
            var root = head;
            while (root >= 2 and tags[root - 1] == .period and tags[root - 2] == .identifier)
                root -= 2;
            return destinationEscapes(tree, tags, bindings, body_first, body_last, root);
        },
        else => return true,
    }
}

/// True unless the frame-local bound at `name_tok` provably stays inside
/// this frame.  Reuses the rule's existing escape discrimination: a
/// discarded `_ = name` and a local copy are private, every other use
/// reaches a callee or a longer-lived owner.
fn destinationEscapes(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    name_tok: Ast.TokenIndex,
) bool {
    const name = tree.tokenSlice(name_tok);
    const binding = bindings.findAt(name, name_tok) orelse return true;
    // Storage the frame does not own: the caller reads it on the error path.
    if (binding.origin == .param) return true;
    return addressAliasEscapes(tree, tags, body_first, body_last, name, binding.name_token);
}

/// First token of the statement containing `tok`.
///
/// `;` and a block-closing `}` end the scan; a `{` that opens a struct or
/// array initializer does not, so `const holder = Holder{ .spec = &root };`
/// resolves to the declaration rather than to the field initializer.
fn statementHead(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    tok: Ast.TokenIndex,
) Ast.TokenIndex {
    var t = tok;
    while (t > first) {
        t -= 1;
        switch (tags[t]) {
            .semicolon, .r_brace => return t + 1,
            .l_brace => if (!braceOpensInitializer(tags, t)) return t + 1,
            else => {},
        }
    }
    return first;
}

fn braceOpensInitializer(tags: []const std.zig.Token.Tag, lb: Ast.TokenIndex) bool {
    if (lb == 0) return false;
    return switch (tags[lb - 1]) {
        .identifier, .r_paren, .r_bracket, .r_brace, .period, .asterisk => true,
        else => false,
    };
}

fn bindingAliasesRoot(
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    root_name: []const u8,
    depth: u8,
) bool {
    if (depth >= 8) return false;
    return switch (binding.origin) {
        .addr_of => |source| std.mem.eql(u8, source, root_name),
        .alias => |source| blk: {
            const source_binding = bindings.findAt(source, binding.rhs_first) orelse
                break :blk false;
            break :blk bindingAliasesRoot(bindings, source_binding, root_name, depth + 1);
        },
        else => false,
    };
}

fn addressAliasEscapes(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    alias_name: []const u8,
    alias_tok: Ast.TokenIndex,
) bool {
    var t = alias_tok + 1;
    while (t < last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), alias_name))
            continue;
        if (t > first and tags[t - 1] == .period) continue;
        // Discarding an alias is not an escape.
        if (t >= 2 and tags[t - 1] == .equal and
            tags[t - 2] == .identifier and std.mem.eql(u8, tree.tokenSlice(t - 2), "_"))
            continue;
        // Copying an alias to another local is followed through by the
        // LocalBindings chain; the copy itself is not the escape.
        if (isLocalAliasCopy(tags, t, first)) continue;
        return true;
    }
    return false;
}

fn isLocalAliasCopy(
    tags: []const std.zig.Token.Tag,
    alias_tok: Ast.TokenIndex,
    first: Ast.TokenIndex,
) bool {
    if (alias_tok < first + 3 or tags[alias_tok - 1] != .equal or
        tags[alias_tok - 2] != .identifier)
        return false;
    const name_tok = alias_tok - 2;
    if (name_tok == first) return false;
    return tags[name_tok - 1] == .keyword_const or tags[name_tok - 1] == .keyword_var;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    try_tok: Ast.TokenIndex,
) !void {
    const msg = try gpa.dupe(u8, "`try` inside single-field union literal assignment — if the error propagates, the tag is written but the payload is left from the previous variant; hoist the `try` before the literal");
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, try_tok),
        .end = try Pos.fromTokenEnd(tree, try_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "tagged-union-payload-early-exit: try in single-field literal fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Self = struct {
        \\    state: union(enum) { ok: u32, err: u32 },
        \\    pub fn run(self: *Self) !void {
        \\        self.state = .{ .err = try computeErr() };
        \\    }
        \\};
        \\fn computeErr() !u32 { return 0; }
        \\
    );
}

test "tagged-union-payload-early-exit: no try does not fire" {
    try testing.expectNoFire(check,
        \\const Self = struct {
        \\    state: union(enum) { ok: u32, err: u32 },
        \\    pub fn run(self: *Self) void {
        \\        self.state = .{ .err = computeErr() };
        \\    }
        \\};
        \\fn computeErr() u32 { return 0; }
        \\
    );
}

test "tagged-union-payload-early-exit: const declaration with try does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn run() !void {
        \\    const x = .{ .err = try f() };
        \\    _ = x;
        \\}
        \\fn f() !u32 { return 0; }
        \\
    );
}

test "tagged-union-payload-early-exit: multi-field literal with try does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    state: struct { a: u32, b: u32 },
        \\    pub fn run(self: *Self) !void {
        \\        self.state = .{ .a = 1, .b = try f() };
        \\    }
        \\};
        \\fn f() !u32 { return 0; }
        \\
    );
}

test "skript residual: single-field struct target with try does not fire" {
    try testing.expectNoFire(check,
        \\const Box = struct { value: u32 };
        \\const Self = struct {
        \\    box: Box,
        \\    fn update(self: *Self) !void {
        \\        self.box = .{ .value = try compute() };
        \\    }
        \\};
        \\fn compute() !u32 { return 1; }
        \\
    );
}

test "skript residual: unobserved local tagged-union field with try does not fire" {
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    switch (source.metric) {
        \\        .diagonal => |weights| {
        \\            result.metric = .{ .diagonal = try dupe(weights) };
        \\        },
        \\        else => {},
        \\    }
        \\    return result;
        \\}
        \\fn dupe(weights: []const f64) ![]const f64 { return weights; }
        \\
    );
}

test "skript residual: observed local tagged-union field with try still fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct {
        \\    metric: Metric,
        \\    fn deinit(self: *SpaceSpec) void { _ = self.metric; }
        \\};
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    errdefer result.deinit();
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "skript residual: pointer-owned tagged-union field with try still fires" {
    try testing.expectFires(check, R,
        \\const State = union(enum) { ready: u32, failed: u32 };
        \\const Self = struct {
        \\    state: State,
        \\    fn update(self: *Self) !void {
        \\        self.state = .{ .failed = try compute() };
        \\    }
        \\};
        \\fn compute() !u32 { return 1; }
        \\
    );
}

test "skript residual: explicit local tagged-union field with try does not fire" {
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneRegistration(source: SpaceSpec) !SpaceSpec {
        \\    var result: SpaceSpec = .{ .metric = .none };
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "skript residual: plain defer observer still fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct {
        \\    metric: Metric,
        \\    fn deinit(self: *SpaceSpec) void { _ = self.metric; }
        \\};
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    defer result.deinit();
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "skript residual: escaped address alias still fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn observe(_: *SpaceSpec) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    const alias = &result;
        \\    observe(alias);
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

// ── Address publication and frame privacy ─────────────────────
//
// `assignmentIsObservable` suppresses a by-value local whose union
// field is written only inside the frame that owns it: on the error
// path that frame dies with nothing able to read the half-retagged
// union.  That proof holds only while the storage stays private.
//
// The question is never "was `&root` written down" — `_ = &root;` and
// a frame-local aggregate holding it are both private — but "where did
// it go".  A callee that receives it, a `defer`/`errdefer`, a
// `return`, or a store into storage the frame does not own all publish.
// The reader that matters is one running while the frame is still
// unwinding, not a use of the pointer after the frame's storage is gone.
//
// `hasEscapedAddressAlias` only inspects NAME bindings, so a direct
// `&root` that is never bound to a local slipped through the
// suppression entirely.  Every publication shape below must report,
// and every shape that keeps the storage frame-private must not.
//
// Semantic premise (both compiler versions tested perform partial
// retagging; do not assume RHS evaluation is transactional):
// docs/superpowers/plans/2026-09-20-zbc-deficiencies.md:304-306.

test "tagged-union-payload-early-exit: address handed to a callee before the assignment fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn observe(_: *SpaceSpec) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    observe(&result);
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: address stored into a longer-lived owner before the assignment fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\const Registry = struct { saved: ?*SpaceSpec = null };
        \\fn cloneSpec(source: SpaceSpec, registry: *Registry) !SpaceSpec {
        \\    var result = source;
        \\    registry.saved = &result;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: address published only after the assignment stays quiet" {
    // On the error path control never reaches `observe` — the `try`
    // leaves the function first — so a publication AFTER the write
    // cannot see a half-retagged union.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn observe(_: *SpaceSpec) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    observe(&result);
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: address bound but never published stays quiet" {
    // `const alias = &result; _ = alias;` reaches nothing outside the
    // frame.  The direct-publication path must keep the existing
    // discard discrimination rather than flag every `&root`.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    const alias = &result;
        \\    _ = alias;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: address of an unrelated local does not make the assignment observable" {
    // Publication is tracked per root: an address of some other
    // local says nothing about `result`'s privacy.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn observe(_: *SpaceSpec) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    var scratch: SpaceSpec = .{ .metric = .none };
        \\    observe(&scratch);
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: address packed into a published aggregate fires" {
    // `&root` buried in a struct-literal field is not the whole
    // initializer of an aliasing declaration, so no binding records
    // it and the escape chain cannot follow it.  The raw occurrence is
    // the only evidence available, and it must not be suppressed.
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\const Holder = struct { spec: *SpaceSpec };
        \\fn observe(_: *Holder) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    const holder = Holder{ .spec = &result };
        \\    observe(&holder);
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: typed alias declaration that is discarded stays quiet" {
    // `const p: *SpaceSpec = &result;` binds the address to a name
    // exactly like the untyped form, and the name is then discarded, so
    // the address stays frame-private.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    const p: *SpaceSpec = &result;
        \\    _ = p;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: address discarded outright stays quiet" {
    // `_ = &result;` drops the pointer before anything can reach it.
    // Flagging the bare occurrence as publication would report a local
    // whose address never left the frame.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    _ = &result;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: private aggregate holding the address stays quiet" {
    // The address is buried in a frame-local aggregate that is itself
    // dropped: the destination is `holder`, not `&result`.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\const Holder = struct { spec: *SpaceSpec };
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    const holder = Holder{ .spec = &result };
        \\    _ = holder;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: binary and on a field of the root stays quiet" {
    // `bits & result.mask` is a binary operator, not an address
    // expression.  Only an `address_of` node may count as publication,
    // so the scan must not read it off the `&` token.
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { mask: u32, metric: Metric };
        \\fn cloneSpec(source: SpaceSpec, bits: u32) !SpaceSpec {
        \\    var result = source;
        \\    const keep = bits & result.mask;
        \\    _ = keep;
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "tagged-union-payload-early-exit: grouped address handed to a callee fires" {
    // `&(result)` is the same address expression as `&result`; the
    // parentheses must not hide it.
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn observe(_: *SpaceSpec) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    observe(&(result));
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

// ── Issue #54 pair ───────────────────────────────────────────
//
// Private construction whose only failing-path cleanup releases raw
// storage is NOT observable partial retagging (safe half).  A union
// the caller owns and inspects after the early exit IS (unsafe
// half), and the diagnostic points at the `try` that can exit.

test "tagged-union-payload-early-exit: private union construction freed raw on every failing path stays quiet" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const State = union(enum) { empty, payload: u32 };
        \\fn compute() error{Failed}!u32 { return error.Failed; }
        \\pub fn build(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(State, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .payload = try compute() };
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: heap union written through a bound pointer stays quiet" {
    // Same privacy proof as above, reached through a named `&slice[i]`
    // instead of the index form: the binding looks like a pointer
    // alias, but the only owner is the frame's `gpa.free`, which runs
    // before the error escapes and never reads the union element.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const State = union(enum) { empty, payload: u32 };
        \\fn compute() error{Failed}!u32 { return error.Failed; }
        \\fn buildThroughAlias(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(State, 1);
        \\    defer gpa.free(fields);
        \\    const first = &fields[0];
        \\    first.* = .{ .payload = try compute() };
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: caller-visible union payload reports the try span" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Msg = struct { text: []const u8 };
        \\fn fromJS(_: usize) !Msg { return error.Failed; }
        \\const Resolve = struct { value: union(enum) { pending, err: Msg } };
        \\fn onError(resolve: *Resolve, exception: usize) !void {
        \\    resolve.value = .{ .err = try fromJS(exception) };
        \\}
        \\
    );
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    // The span is the `try` token itself (line 5, column 31), not the
    // whole assignment: only the payload expression can exit early.
    const found = problems.items[0];
    try std.testing.expectEqual(@as(u32, 5), found.start.line);
    try std.testing.expectEqual(@as(u32, 31), found.start.column);
    try std.testing.expectEqual(found.start.line, found.end.line);
    try std.testing.expectEqual(@as(u32, "try".len), found.end.byte - found.start.byte);
}

// ── Loop captures and the storage they write through ──────────
//
// `for (fields) |*field| { field.kind = .{ … try … } }` retags an
// ELEMENT of `fields`.  The write lands in `fields`' storage, so the
// privacy question is about that storage: who owns it, what runs on
// the failing path, and what was handed the slice before the write.
//
// ocean's `decodeModuleLayouts` is the quiet half — a fresh `alloc`
// released raw by the `errdefer` on every failing path, published
// into `module.layouts` only after the loop finishes.  Every loud
// half below differs in exactly one of those three facts.

test "tagged-union-payload-early-exit: loop capture over a raw-freed allocation stays quiet" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16, bit_width: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(allocator: std.mem.Allocator, count: usize) !void {
        \\    var fields: []Field = &.{};
        \\    if (count != 0) {
        \\        fields = allocator.alloc(Field, count) catch return error.OutOfMemory;
        \\    }
        \\    errdefer if (fields.len != 0) allocator.free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16(), .bit_width = 1 } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: loop capture over a caller-owned slice still fires" {
    // The iterable is a parameter: the caller owns the elements and
    // reads them on the error path, whatever this frame does with the
    // slice itself.
    try testing.expectFires(check, R,
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn update(fields: []Field) !void {
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: storage published before the write still fires" {
    // Same allocation, same raw release — but the slice reached
    // `sink` before the loop, so the caller can read the element
    // after the frame returns the error.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator, sink: *[]Field) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    sink.* = fields;
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a cleanup that reads the captured element still fires" {
    // The raw release is there, and so is a second cleanup that
    // inspects the element the retag just corrupted.  That observer
    // runs on the failing path, so privacy is not proved.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn trace(kind: FieldKind) void { _ = kind; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    errdefer trace(fields[0].kind);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: an unreleased capture still fires" {
    // Privacy is proved by the release, not by the allocation alone:
    // with nothing registered to give the storage back, the rule
    // reports rather than assume.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a capture over an unplaceable iterable still fires" {
    // `self.fields` is not a nameable storage: the rule cannot tell
    // who owns the elements, so it must not treat the capture as
    // private.  Exempting every loop capture would silence this.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\const Self = struct { gpa: std.mem.Allocator, fields: []Field };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(self: *Self) !void {
        \\    defer self.gpa.free(self.fields);
        \\    for (self.fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

// ── Who proved the release ──────────────────────────────────
//
// The quiet half of the capture rule is made of one fact: the cleanup
// that keeps the retag unobserved is a release that RESOLVES to the
// standard allocator, registered in a block that is an ANCESTOR of the
// block the write is written in, on a path that always reaches the
// write.  Each test below breaks exactly one of those, and each breaks
// it in a direction that must be LOUD.

test "tagged-union-payload-early-exit: a release in an enclosing block resolves the allocator and stays quiet" {
    // ocean's `decodeModuleLayouts` shape.  The errdefer is registered
    // in the `while` body and the write is inside the `for` body nested
    // in it, so the release's block is an ANCESTOR of the write's.
    // The errdefer is also preceded by `}` — the closing brace of the
    // braced allocation `if` — rather than by `;`, so this covers the
    // one predecessor shape a sibling block cannot reach.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16, bit_width: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(allocator: std.mem.Allocator, count: usize) !void {
        \\    var index: usize = 0;
        \\    while (index < count) : (index += 1) {
        \\        var fields: []Field = &.{};
        \\        if (count != 0) {
        \\            fields = allocator.alloc(Field, count) catch return error.OutOfMemory;
        \\        }
        \\        errdefer if (fields.len != 0) allocator.free(fields);
        \\        for (fields) |*field| {
        \\            field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\        }
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a release through an allocator alias still resolves" {
    // The receiver is not spelled `std.mem.Allocator`; it is a `const`
    // bound to one.  Resolution reads the DECLARED TYPE through the
    // alias, which is why an alias counts and a look-alike does not.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const arena = gpa;
        \\    const fields = try arena.alloc(Field, 1);
        \\    defer arena.free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a release in a sibling block does not dominate the write" {
    // Same depth as the loop, different block.  A brace count cannot
    // tell these apart, and reading it as enclosing is what let the
    // sibling's scope end before the write ran.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    {
        \\        errdefer gpa.free(fields);
        \\    }
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a release in a mutually exclusive arm does not dominate the write" {
    // The errdefer is armed only when `flag` holds, and the write runs
    // only in the `else`.  Both blocks sit at the same depth, and on no
    // failing path are they both live.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator, flag: bool) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    if (flag) {
        \\        errdefer gpa.free(fields);
        \\    } else {
        \\        for (fields) |*field| {
        \\            field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\        }
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a release registered after the write does not cover it" {
    // The release is in the right block and resolves, but it is
    // registered after the statement whose `try` can exit, so on the
    // failing path nothing had released the storage yet.  A braceless
    // `if (flag) errdefer …;` would be the same mistake, and Zig's
    // grammar rejects it — a defer is a block item, never a prong body
    // — so the ancestor-block proof is what refuses every conditional
    // arm that does not enclose the write.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\        errdefer gpa.free(fields);
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a release through a destructor is not a raw release" {
    // `deinit` can run code that dispatches on the element, so the
    // slice it was handed is an ordinary read in the cleanup.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\const Owner = struct {
        \\    fn deinit(self: *Owner, items: []Field) void { _ = self; _ = items; }
        \\};
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator, owner: *Owner) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer owner.deinit(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a user free that inspects the union is an observer, not a raw release" {
    // `free` here is a function in this file, not the allocator's
    // method.  The receiver is absent, so nothing resolves it, and the
    // slice it was handed is an ordinary read in the cleanup.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn trace(kind: FieldKind) void { _ = kind; }
        \\fn free(fields: []Field) void { trace(fields[0].kind); }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    errdefer free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a user free that does not inspect the union is still not a raw release" {
    // The pin for the other direction.  A callee this rule cannot
    // resolve is not evidence of privacy, whether or not its body would
    // have been harmless: the privacy proof is made of a RESOLVED
    // release, and an unresolved one lands on the report side.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn free(fields: []Field) void { _ = fields; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    errdefer free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a free method on a non-allocator type is not a raw release" {
    // `Pool.free` is a method on a type declared here.  Its receiver
    // resolves, and to something that is not `std.mem.Allocator`.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\const Pool = struct {
        \\    fn free(self: Pool, fields: []Field) void { _ = self; _ = fields; }
        \\};
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator, pool: Pool) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    errdefer pool.free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a release whose receiver is a struct field is not resolved" {
    // `self.gpa` is a field path, not the plain name whose declared
    // type this walk reads.  Unresolved is the report side.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\const Self = struct { gpa: std.mem.Allocator };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(self: *Self) !void {
        \\    const fields = try self.gpa.alloc(Field, 1);
        \\    defer self.gpa.free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: an anytype allocator is not a resolved receiver" {
    // A generic parameter declares no allocator type, so resolution
    // fails and the failure is reported rather than assumed private.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(alloc: anytype) !void {
        \\    const fields = try alloc.alloc(Field, 1);
        \\    defer alloc.free(fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: one cleanup that releases raw and then reads is still an observer" {
    // The release and the read share a statement.  The release hands
    // the bytes back; the `trace` after it still dispatches on the
    // union the retag flipped, so privacy is not proved.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn trace(kind: FieldKind) void { _ = kind; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    errdefer { gpa.free(fields); trace(fields[0].kind); }
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a capture handed to a callee before the write still fires" {
    // The storage is private and released raw, and the loop capture is
    // still a pointer to the element the retag corrupts: handing it to
    // a callee publishes the union as surely as handing the slice does.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn observe(field: *Field) void { _ = field; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    for (fields) |*field| {
        \\        observe(field);
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: reading or writing the capture in place stays quiet" {
    // The other side of that boundary.  A test on the capture and a
    // plain write through it both stay inside the loop body; neither
    // reaches a callee, so neither publishes anything.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const BitInfo = struct { bit_offset: u16 };
        \\const FieldKind = union(enum) { ordinary, bit_field: BitInfo };
        \\const Field = struct { kind: FieldKind, byte_offset: u64 };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .kind = .{ .bit_field = .{ .bit_offset = 0 } }, .byte_offset = 0 };
        \\    for (fields) |*field| {
        \\        if (field.kind == .ordinary) continue;
        \\        field.byte_offset = 1;
        \\        field.kind = .{ .bit_field = .{ .bit_offset = try readU16() } };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: initialized private element construction stays quiet" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const FieldKind = union(enum) { ordinary, bit_field: u16 };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .kind = .ordinary };
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = try readU16() };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: grouped capture reads are not call arguments" {
    // The initial element write stays inside freshly allocated storage.
    // On failure only the raw release runs; neither grouped read is a call.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const FieldKind = union(enum) { ordinary, bit_field: u16 };
        \\const Field = struct { kind: FieldKind, byte_offset: u64 };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .kind = .ordinary, .byte_offset = 0 };
        \\    for (fields) |*field| {
        \\        _ = (field.kind);
        \\        if ((field.kind) == .ordinary) field.byte_offset = 1;
        \\        field.kind = .{ .bit_field = try readU16() };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: grouped capture call arguments still publish" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FieldKind = union(enum) { ordinary, bit_field: u16 };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn publish(sink: *?*Field, field: *Field) void { sink.* = field; }
        \\fn decode(gpa: std.mem.Allocator, sink: *?*Field) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .kind = .ordinary };
        \\    for (fields) |*field| {
        \\        publish(sink, (field));
        \\        field.kind = .{ .bit_field = try readU16() };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a grouped payload read during cleanup still observes" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FieldKind = union(enum) { ordinary, bit_field: u16 };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn decode(gpa: std.mem.Allocator, sink: *u16) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .kind = .ordinary };
        \\    for (fields) |*field| {
        \\        errdefer sink.* = (field.kind.bit_field);
        \\        field.kind = .{ .bit_field = try readU16() };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: an indexed element handed to a callee still publishes" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FieldKind = union(enum) { ordinary, bit_field: u16 };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn publish(sink: *?*Field, field: *Field) void { sink.* = field; }
        \\fn decode(gpa: std.mem.Allocator, sink: *?*Field) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = .{ .kind = .ordinary };
        \\    publish(sink, &fields[0]);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = try readU16() };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: an element initializer can publish its storage" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FieldKind = union(enum) { ordinary, bit_field: u16 };
        \\const Field = struct { kind: FieldKind };
        \\fn readU16() error{EndOfStream}!u16 { return error.EndOfStream; }
        \\fn publish(sink: *[]Field, fields: []Field) Field {
        \\    sink.* = fields;
        \\    return .{ .kind = .ordinary };
        \\}
        \\fn decode(gpa: std.mem.Allocator, sink: *[]Field) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    fields[0] = publish(sink, fields);
        \\    for (fields) |*field| {
        \\        field.kind = .{ .bit_field = try readU16() };
        \\    }
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: a reached plain-root heap construction stays quiet" {
    // `fields[0] = …` ends in `]` and `first.* = …` in `*`, so the LHS
    // walk skips both before any privacy question is asked and neither
    // exercises anything.  Naming the target directly is what makes
    // this the same proof with the root actually reached.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const State = union(enum) { empty, payload: u32 };
        \\fn compute() error{Failed}!u32 { return error.Failed; }
        \\fn build(gpa: std.mem.Allocator) !void {
        \\    const fields = try gpa.alloc(State, 1);
        \\    var slot: State = .empty;
        \\    defer gpa.free(fields);
        \\    slot = .{ .payload = try compute() };
        \\    fields[0] = slot;
        \\}
        \\
    );
}

test "tagged-union-payload-early-exit: inferred private result retains its frame boundary" {
    try testing.expectNoFireTyped(check,
        \\const State = union(enum) { empty, ready: u32 };
        \\const Request = struct { state: State, prefix: u8 };
        \\fn base() Request { return .{ .state = .empty, .prefix = 0 }; }
        \\fn payload(prefix: *u8) !u32 { prefix.* = 1; return error.Failed; }
        \\fn build() !Request {
        \\    var result = base();
        \\    result.state = .{ .ready = try payload(&result.prefix) };
        \\    return result;
        \\}
    );
}

test "tagged-union-payload-early-exit: inferred private result published before retag still warns" {
    try testing.expectFiresTyped(check, R,
        \\const State = union(enum) { empty, ready: u32 };
        \\const Request = struct { state: State };
        \\fn base() Request { return .{ .state = .empty }; }
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(sink: **Request) !Request {
        \\    var result = base();
        \\    sink.* = &result;
        \\    result.state = .{ .ready = try payload() };
        \\    return result;
        \\}
    );
}

test "tagged-union-payload-early-exit: optional borrowed reader is a struct not a union" {
    try testing.expectNoFireTyped(check,
        \\const Reader = struct { bytes: []const u8 };
        \\const Cursor = struct {
        \\    reader: ?Reader = null,
        \\    fn load(self: *Cursor) !void {
        \\        self.reader = .{ .bytes = try payload() };
        \\    }
        \\};
        \\fn payload() ![]const u8 { return error.Failed; }
    );
}

test "tagged-union-payload-early-exit: optional published union is not a borrowed-reader exemption" {
    try testing.expectFiresTyped(check, R,
        \\const Reader = union(enum) { empty, bytes: []const u8 };
        \\const Cursor = struct {
        \\    reader: ?Reader = null,
        \\    fn load(self: *Cursor) !void {
        \\        self.reader = .{ .bytes = try payload() };
        \\    }
        \\};
        \\fn payload() ![]const u8 { return error.Failed; }
    );
}

test "tagged-union-payload-early-exit: private arena element with disjoint cleanup stays quiet" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Provenance = union(enum) { derived, acquired: []const u8 };
        \\const Source = struct { lease: u32, provenance: Provenance };
        \\fn release(_: u32) void {}
        \\fn build(gpa: std.mem.Allocator) !void {
        \\    var region = std.heap.ArenaAllocator.init(gpa);
        \\    errdefer region.deinit();
        \\    const memory = region.allocator();
        \\    const sources = try memory.alloc(Source, 1);
        \\    sources[0] = .{ .lease = 1, .provenance = .{ .acquired = "path" } };
        \\    errdefer for (sources[0..1]) |source| release(source.lease);
        \\    for (sources[0..1]) |*source| {
        \\        source.provenance = .{ .acquired = try memory.dupe(u8, "path") };
        \\    }
        \\}
    );
}

test "tagged-union-payload-early-exit: arena cleanup reading retagged field still warns" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Provenance = union(enum) { derived, acquired: []const u8 };
        \\const Source = struct { lease: u32, provenance: Provenance };
        \\fn observe(_: Provenance) void {}
        \\fn build(gpa: std.mem.Allocator) !void {
        \\    var region = std.heap.ArenaAllocator.init(gpa);
        \\    errdefer region.deinit();
        \\    const memory = region.allocator();
        \\    const sources = try memory.alloc(Source, 1);
        \\    errdefer for (sources[0..1]) |source| observe(source.provenance);
        \\    for (sources[0..1]) |*source| {
        \\        source.provenance = .{ .acquired = try memory.dupe(u8, "path") };
        \\    }
        \\}
    );
}

test "tagged-union-payload-early-exit: copied caller storage is not a private allocation" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Kind = union(enum) { empty, value: u32 };
        \\const Field = struct { kind: Kind };
        \\fn payload() !u32 { return error.Failed; }
        \\fn update(gpa: std.mem.Allocator, caller_fields: []Field) !void {
        \\    const fields: []Field = caller_fields;
        \\    defer gpa.free(fields);
        \\    for (fields) |*field| field.kind = .{ .value = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: raw release through another allocator is not owning cleanup" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Kind = union(enum) { empty, value: u32 };
        \\const Field = struct { kind: Kind };
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(first: std.mem.Allocator, second: std.mem.Allocator) !void {
        \\    const fields = try first.alloc(Field, 1);
        \\    defer second.free(fields);
        \\    for (fields) |*field| field.kind = .{ .value = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: raw free argument must be the exact allocation" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Kind = union(enum) { empty, value: u32 };
        \\const Field = struct { kind: Kind };
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(gpa: std.mem.Allocator, unrelated: [][]Field) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(unrelated[fields.len]);
        \\    for (fields) |*field| field.kind = .{ .value = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: six mapped cleanup variants remain unsafe" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const std = @import("std");
        \\const Frozen = union(enum) {
        \\    combinational: []u8,
        \\    lookup_table: []u8,
        \\    sequential: []u8,
        \\    memory: []u8,
        \\    global_buffer: []u8,
        \\    physical_only: []u8,
        \\    fn release(self: Frozen, memory: std.mem.Allocator) void {
        \\        switch (self) {
        \\            inline else => |bytes| memory.free(bytes),
        \\        }
        \\    }
        \\};
        \\fn copy(memory: std.mem.Allocator, which: u8) !Frozen {
        \\    var result: Frozen = .{ .physical_only = &.{} };
        \\    errdefer result.release(memory);
        \\    switch (which) {
        \\        0 => result = .{ .combinational = try memory.alloc(u8, 1) },
        \\        1 => result = .{ .lookup_table = try memory.alloc(u8, 1) },
        \\        2 => result = .{ .sequential = try memory.alloc(u8, 1) },
        \\        3 => result = .{ .memory = try memory.alloc(u8, 1) },
        \\        4 => result = .{ .global_buffer = try memory.alloc(u8, 1) },
        \\        else => result = .{ .physical_only = try memory.alloc(u8, 1) },
        \\    }
        \\    return result;
        \\}
    );
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 6), problems.items.len);
    for (problems.items) |problem| try std.testing.expectEqualStrings(R, problem.rule_id);
}

test "tagged-union-payload-early-exit: publication inside the fallible payload still warns" {
    try testing.expectFiresTyped(check, R,
        \\const State = union(enum) { empty, ready: u32 };
        \\const Request = struct { state: State };
        \\fn base() Request { return .{ .state = .empty }; }
        \\fn publishAndFail(request: *Request, sink: **Request) !u32 {
        \\    sink.* = request;
        \\    return error.Failed;
        \\}
        \\fn build(sink: **Request) !Request {
        \\    var result = base();
        \\    result.state = .{ .ready = try publishAndFail(&result, sink) };
        \\    return result;
        \\}
    );
}

test "tagged-union-payload-early-exit: storing a capture pointer publishes the private element" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Kind = union(enum) { empty, value: u32 };
        \\const Field = struct { kind: Kind };
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(gpa: std.mem.Allocator, sink: **Field) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    for (fields) |*field| {
        \\        sink.* = field;
        \\        field.kind = .{ .value = try payload() };
        \\    }
        \\}
    );
}

test "tagged-union-payload-early-exit: a field address can expose the enclosing union storage" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Kind = union(enum) { empty, value: u32 };
        \\const Field = struct { kind: Kind, marker: u32 };
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(gpa: std.mem.Allocator, sink: **u32) !void {
        \\    const fields = try gpa.alloc(Field, 1);
        \\    defer gpa.free(fields);
        \\    for (fields) |*field| {
        \\        sink.* = &((field.marker));
        \\        field.kind = .{ .value = try payload() };
        \\    }
        \\}
    );
}

test "tagged-union-payload-early-exit: mutable allocator header is not an exact owning path" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Kind = union(enum) { empty, value: u32 };
        \\const Field = struct { kind: Kind };
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(memory: *std.mem.Allocator, other: std.mem.Allocator) !void {
        \\    const fields = try memory.alloc(Field, 1);
        \\    defer memory.free(fields);
        \\    memory.* = other;
        \\    for (fields) |*field| field.kind = .{ .value = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: a private header does not own an intermediate pointee" {
    try testing.expectFiresTyped(check, R,
        \\const State = union(enum) { empty, ready: u32 };
        \\const Owner = struct { state: State };
        \\const Header = struct { borrowed: *Owner };
        \\fn payload() !u32 { return error.Failed; }
        \\fn update(owner: *Owner) !void {
        \\    var local: Header = .{ .borrowed = owner };
        \\    local.borrowed.state = .{ .ready = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: an annotated pointer alias is not private value storage" {
    try testing.expectFires(check, R,
        \\const State = union(enum) { empty, ready: u32 };
        \\const Owner = struct { state: State };
        \\const Alias = *Owner;
        \\fn payload() !u32 { return error.Failed; }
        \\fn update(owner: *Owner) !void {
        \\    const local: Alias = owner;
        \\    local.state = .{ .ready = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: raw allocation cleanup binder is not an element read" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const State = union(enum) { empty, ready: u32 };
        \\const Item = struct { lease: u32, state: State };
        \\fn release(_: u32) void {}
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(memory: std.mem.Allocator) !void {
        \\    const items = try memory.alloc(Item, 1);
        \\    errdefer memory.free(items);
        \\    items[0] = .{ .lease = 1, .state = .empty };
        \\    errdefer { for (items) |item| release(item.lease); }
        \\    for (items) |*item| item.state = .{ .ready = try payload() };
        \\}
    );
}

test "tagged-union-payload-early-exit: cleanup binder does not hide a whole-element observer" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const State = union(enum) { empty, ready: u32 };
        \\const Item = struct { lease: u32, state: State };
        \\fn observe(_: Item) void {}
        \\fn payload() !u32 { return error.Failed; }
        \\fn build(memory: std.mem.Allocator) !void {
        \\    const items = try memory.alloc(Item, 1);
        \\    errdefer memory.free(items);
        \\    items[0] = .{ .lease = 1, .state = .empty };
        \\    errdefer { for (items) |item| observe(item); }
        \\    for (items) |*item| item.state = .{ .ready = try payload() };
        \\}
    );
}
