//! oven-sh/bun#30169 detector — `const X = try <Type>.<method>(...);`
//! followed by another `try` in the same function body with NO
//! `errdefer X.deinit();` registered between.  If the second try
//! propagates an error, X's allocation leaks.
//!
//! Detection (per-fn binding-walk):
//!   1. Find every `const X = try …<Type>.<method>(...)` binding
//!      where `<method>` ∈ {fromJS} (ownership transfer) OR an
//!      fd-opener (createFile/openFile/...).
//!   2. For ownership-transfer methods, require `<Type>` to be
//!      title-cased AND to have a `deinit` (or be unknown — we
//!      pass through cross-file types conservatively).
//!   3. At the next failure, require an active cleanup of the exact
//!      binding/value. Copies retain their capture-time identity.
//!   4. A field publication can inherit caller cleanup only through a
//!      complete declaration-bound caller census and actual-argument map.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const file_model = @import("../../model/file_model.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "missing-errdefer-between-tries";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .missing_errdefer_between_tries)) return;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();

    const model = try cache.fileModel();
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try checkFn(gpa, tree, cache, model, fn_entry.proto, fn_entry.body, problems);
    }
}

const TrackedBinding = struct {
    x_name: []const u8,
    name_token: Ast.TokenIndex,
    /// Token of the binding's terminating semicolon — scans for
    /// subsequent `try` / `errdefer` start from after this.
    end_token: Ast.TokenIndex,
    is_fd_open: bool,
    /// True iff the binding is a control-flow capture (`if (try ...)
    /// |x|`, `while (try ...) |x|`, `catch |err|`).  Captures are
    /// scoped to the body that follows the `|...|` — the scan must
    /// step INTO that body and break on its closing brace, not on
    /// the enclosing fn block's brace.
    is_capture: bool,
};

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);

    // Cheap pre-scan: skip fns with no `try` at all.
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    if (!tokens.hasTokenInRange(tags, first, last, .keyword_try)) return;

    const bindings = (try cache.localBindings(proto, body)).*;

    var tracked: std.ArrayListUnmanaged(TrackedBinding) = .empty;
    defer tracked.deinit(gpa);

    for (bindings.items) |b| {
        if (!b.is_const) continue;
        if (b.origin == .param) continue;
        // Must be a try-wrapped binding.  Includes captures
        // (`if (try Loader.fromJS(...)) |x|`) AND const bindings
        // (`const X = try ...`).
        if (!b.wasTryWrapped(tags)) continue;
        // Arena-allocated bindings: if the RHS passes
        // `<arena>.allocator()` and the fn body has a `defer
        // <arena>.deinit();` in scope, the binding's storage is
        // already cleaned up unconditionally on any return path —
        // no errdefer needed.  Canonical Bun shape:
        //     var arena = ArenaAllocator.init(...);
        //     defer arena.deinit();
        //     const x = try foo(arena.allocator(), ...);
        if (try rhsArenaIsDeferDeinited(cache, &bindings, body, b)) continue;

        // Extract the FIRST call's (type, method) — the OLD walker
        // semantics.  Works for any rhs shape including chains and
        // loop-capture scrutinees.
        const parsed = parseTypeMethodAfter(tree, b.rhs_first + 1, b.rhs_last) orelse continue;

        // For chained calls like `std.fs.cwd().createFile(...)`,
        // the FIRST method (cwd) isn't an opener but the OUTER call
        // (createFile) is.  When asCall is available (.try_method_call
        // origins), check the outermost method as a fallback.
        var meth = parsed.method;
        if (!isOwnershipTransferMethod(meth) and !isFileHandleOpenerMethod(meth)) {
            if (b.asCall()) |c| {
                if (c.outermost_method) |outer| {
                    if (isFileHandleOpenerMethod(outer)) meth = outer;
                }
            }
        }

        var is_fd_open = false;
        if (isOwnershipTransferMethod(meth)) {
            if (parsed.type_name.len == 0 or parsed.type_name[0] < 'A' or parsed.type_name[0] > 'Z') continue;
            if (!typeHasDeinitProject(cache, model, parsed.type_name)) continue;
            // Refine via the binding's explicit `: <Type>`
            // annotation when present.  When the LHS type is in
            // the file model AND demonstrably has no deinit, the
            // value doesn't need cleanup regardless of what the
            // RHS' fromJS / fromXxx returns.  This catches cases
            // where parsed.type_name resolves to a generic
            // namespace like `bun.SignalCode` (we'd see "SignalCode"
            // as the RHS type; cross-file means we can't refute).
            if (typeAnnotationLacksDeinit(tree, b, model)) continue;
            // Switch-scrutinee shape skip: when the binding is
            // IMMEDIATELY consumed by `switch (<name>) { .<tag> =>
            // ..., .<tag> => ..., }` with payload-less arms, the
            // value is an enum tag — no cleanup needed.  Catches
            // cross-file enum types whose declaration we can't
            // see (`bun.SignalCode`, `types.Tag`).
            if (consumedAsEnumSwitch(tree, tags, b, last)) continue;
            // ZLS fallback: ask ZLS for the binding's RHS type.
            // When the RHS is `<ns>.<Type>.fromJS(...)` and `<ns>`
            // is an imported namespace, the local model can't see
            // `<Type>` — but ZLS can resolve through @import.
            // If the resolved type is locally known AND has no
            // deinit, skip.  If unresolvable, fall through and
            // fire (conservative).
            if (rhsTypeViaZlsLacksDeinit(cache, model, tags, b)) continue;
        } else if (isFileHandleOpenerMethod(meth)) {
            is_fd_open = true;
            // Ownership is checked at the actual later failure, not by
            // searching for a future wrapper/defer anywhere in the body.
        } else continue;

        try tracked.append(gpa, .{
            .x_name = b.name,
            .name_token = b.name_token,
            // local.Binding.rhs_last is the token before `;`.
            .end_token = b.rhs_last + 1,
            .is_fd_open = is_fd_open,
            .is_capture = b.origin == .loop_capture,
        });
    }

    for (tracked.items) |b| {
        var has_cleanup = false;
        var found_try = false;
        // Track brace depth so the scan stops when the binding leaves
        // scope.  Two cases:
        //   - const/var binding: scope extends to the enclosing block's
        //     `}`.  Scan starts at end_token+1 (already inside the
        //     block); we break when depth dips below 0.
        //   - capture (`if (try ...) |x| { ... }`): scope is the body
        //     braces themselves.  Advance the scan past the opening
        //     `{` so depth=0 there means "still inside the body"; we
        //     break when the closing `}` pops us back to depth=-1.
        var u: Ast.TokenIndex = b.end_token + 1;
        if (b.is_capture) {
            while (u <= last and tags[u] != .l_brace) : (u += 1) {}
            if (u > last) continue; // malformed; skip
            u += 1; // step inside the body
        }
        var depth: i32 = 0;
        while (u <= last) : (u += 1) {
            switch (tags[u]) {
                .l_brace => depth += 1,
                .r_brace => {
                    depth -= 1;
                    if (depth < 0) break; // left binding's scope
                },
                .keyword_defer, .keyword_errdefer => {
                    // Registration is not execution. In particular a try
                    // inside the deferred body is not this scope's next try.
                    if (deferredNodeAt(tree, u)) |deferred| {
                        u = tree.lastToken(deferred);
                    }
                },
                .keyword_try => {
                    found_try = true;
                    const original = bindings.findAt(b.x_name, b.name_token) orelse break;
                    has_cleanup = try protectedAt(cache, proto, body, original, u);
                    break;
                },
                else => {},
            }
        }
        if (found_try and !has_cleanup) {
            try report(gpa, problems, tree, b);
        }
    }
}


const ParsedCall = struct {
    type_name: []const u8,
    method: []const u8,
};

/// Only the SDK arena accessor and the same active owner cleanup can
/// discharge this obligation. A later or shadowed defer is not proof.
fn rhsArenaIsDeferDeinited(
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    binding: local_bindings.Binding,
) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    const resolver = cache.zls orelse return false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) < binding.rhs_first or tree.lastToken(node) > binding.rhs_last) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const receiver, const method = tree.nodeData(call.ast.fn_expr).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(method), "allocator")) continue;
        const actual = (try resolver.resolutionFrame().containerOfNode(receiver)) orelse continue;
        if (!try resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/ArenaAllocator.zig")) continue;
        const owner = (try expressionTarget(cache, bindings, receiver, binding.rhs_last)) orelse continue;
        if (try activeCleanup(cache, bindings, body, owner, binding.rhs_last)) return true;
    }
    return false;
}

fn parseTypeMethodAfter(tree: *const Ast, start: Ast.TokenIndex, last: Ast.TokenIndex) ?ParsedCall {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    var prev_ident: ?Ast.TokenIndex = null;
    var last_ident: ?Ast.TokenIndex = null;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .identifier => {
                prev_ident = last_ident;
                last_ident = t;
            },
            .period => {},
            .l_paren => break,
            else => return null,
        }
    }
    const pi = prev_ident orelse return null;
    const li = last_ident orelse return null;
    if (pi == li) return null;
    return .{ .type_name = tree.tokenSlice(pi), .method = tree.tokenSlice(li) };
}

/// Restricted to the canonical "convert a JS value into an owned
/// Zig value" entry point — `<Type>.fromJS`.  Bun's strongest
/// ownership-transfer signal; broadening adds many FPs.
fn isOwnershipTransferMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "fromJS");
}

/// Methods that return an owned OS file/socket handle; cleanup is
/// `.close()` rather than `.deinit()`.
fn isFileHandleOpenerMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "createFile") or
        std.mem.eql(u8, name, "createFileZ") or
        std.mem.eql(u8, name, "openFile") or
        std.mem.eql(u8, name, "openFileZ") or
        std.mem.eql(u8, name, "openDir") or
        std.mem.eql(u8, name, "openDirZ") or
        std.mem.eql(u8, name, "openat") or
        std.mem.eql(u8, name, "openatZ") or
        std.mem.eql(u8, name, "socket") or
        std.mem.eql(u8, name, "accept");
}

/// True iff the binding has an explicit `: <Type>` type annotation
/// AND that `<Type>` is a known no-deinit type — a primitive
/// (numeric / bool), an enum tag, or a struct in the file model
/// with no deinit method.  Used to suppress the rule on bindings
/// whose annotated type proves cleanup is unnecessary, even when
/// the RHS's apparent type can't be cross-file-resolved.
fn typeAnnotationLacksDeinit(
    tree: *const Ast,
    b: anytype,
    model: *const file_model.FileModel,
) bool {
    const tags = tree.tokens.items(.tag);
    // Annotation sits between `name_token` and the binding's `=`.
    // The `=` is one token before `rhs_first` (when no `try`) or
    // two before (when leading `try`).  Anchor on the colon.
    var t = b.name_token + 1;
    if (t >= tags.len or tags[t] != .colon) return false;
    t += 1;
    // Walk past `?` / `*` / `const` qualifiers to the first
    // identifier.
    while (t < tags.len) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .asterisk, .keyword_const, .keyword_var => continue,
            .identifier => break,
            else => return false,
        }
    }
    if (t >= tags.len or tags[t] != .identifier) return false;
    const first_id = tree.tokenSlice(t);
    // Primitive numeric / bool: never have deinit.
    if (isPrimitiveBaseName(first_id)) return true;
    // Possibly `bun.Foo` / `bun.api.Foo` etc. — walk a `.<ident>`
    // chain and take the LAST identifier as the type name.
    var last_id = first_id;
    var u: TokenIndex = t + 1;
    while (u + 1 < tags.len and tags[u] == .period and tags[u + 1] == .identifier) {
        last_id = tree.tokenSlice(u + 1);
        u += 2;
    }
    // If the type is in this file's model, ask it directly.
    if (model.hasType(last_id)) {
        return !model.typeHasMethod(last_id, "deinit");
    }
    // Common Bun naming conventions for non-owned scalar types:
    // `SignalCode` / `ErrorCode` / `<X>Code`, `FileFD`, `<X>Id`.
    // Conservative — only trip on suffixes that strongly imply
    // an enum/int alias, not a heap-owning struct.
    if (std.mem.endsWith(u8, last_id, "Code")) return true;
    if (std.mem.endsWith(u8, last_id, "Id") and last_id.len >= 3) return true;
    if (std.mem.endsWith(u8, last_id, "ID") and last_id.len >= 3) return true;
    if (std.mem.endsWith(u8, last_id, "Tag")) return true;
    if (std.mem.endsWith(u8, last_id, "Kind")) return true;
    if (std.mem.endsWith(u8, last_id, "Flags")) return true;
    return false;
}

const TokenIndex = Ast.TokenIndex;

fn isPrimitiveBaseName(name: []const u8) bool {
    if (std.mem.eql(u8, name, "bool")) return true;
    if (std.mem.eql(u8, name, "void")) return true;
    if (std.mem.eql(u8, name, "anyopaque")) return true;
    if (std.mem.eql(u8, name, "usize")) return true;
    if (std.mem.eql(u8, name, "isize")) return true;
    if (std.mem.eql(u8, name, "comptime_int")) return true;
    if (std.mem.eql(u8, name, "comptime_float")) return true;
    if (name.len < 2) return false;
    const lead = name[0];
    if (lead == 'f' or lead == 'u' or lead == 'i') {
        for (name[1..]) |c| if (c < '0' or c > '9') return false;
        return true;
    }
    return false;
}

/// Switch-scrutinee shape inference.  When a try-bound local is
/// IMMEDIATELY (within ~30 tokens) consumed by a switch whose
/// arms are payload-less tag patterns (`.int8 => ...`), the
/// value is an enum tag — no cleanup needed regardless of what
/// the cross-file return type's name resolves to.
fn consumedAsEnumSwitch(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    b: anytype,
    body_last: Ast.TokenIndex,
) bool {
    // Walk forward from the binding's terminating `;` looking for
    // either `switch (<name>)` with payload-less arms OR
    // `@tagName(<name>)` — both signal an enum tag.  Either form
    // up to K=60 tokens (enough to span a single short statement).
    var t: Ast.TokenIndex = b.rhs_last + 1; // step past `;`
    var i: u32 = 0;
    while (t < body_last and i < 60) : ({
        t += 1;
        i += 1;
    }) {
        // `@tagName(<name>)` — only valid for enum/union tags.
        if (tags[t] == .builtin and std.mem.eql(u8, tree.tokenSlice(t), "@tagName")) {
            if (t + 3 <= body_last and tags[t + 1] == .l_paren and
                tags[t + 2] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t + 2), b.name)) return true;
        }
        if (tags[t] != .keyword_switch) continue;
        if (t + 4 > body_last) return false;
        if (tags[t + 1] != .l_paren) return false;
        if (tags[t + 2] != .identifier) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), b.name)) return false;
        if (tags[t + 3] != .r_paren) return false;
        if (tags[t + 4] != .l_brace) return false;
        // Scan arms until matching `}`.  Every arm pattern must be
        // `.<id>` (or `.<id>, .<id> ...`) followed by `=>` — no
        // capture (`|cap|`) means no payload.
        var depth: i32 = 1;
        var u: Ast.TokenIndex = t + 5;
        while (u < body_last and depth > 0) : (u += 1) {
            switch (tags[u]) {
                .l_brace => depth += 1,
                .r_brace => depth -= 1,
                .pipe => if (depth == 1) return false,
                else => {},
            }
        }
        return true;
    }
    return false;
}

/// ZLS-resolved type-of-RHS check.  Strip the leading `try` from
/// the binding's RHS, ask the cache to resolve the call
/// expression's type via ZLS, and return true when the resolved
/// type is locally declared AND demonstrably has no deinit (or
/// is a file-struct with no top-level deinit fn).  Falls through
/// to `false` on unresolved types so the rule stays conservative.
fn rhsTypeViaZlsLacksDeinit(
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    tags: []const std.zig.Token.Tag,
    b: anytype,
) bool {
    var start = b.rhs_first;
    if (start <= b.rhs_last and tags[start] == .keyword_try) start += 1;
    // The binding's RHS may include trailing tokens (e.g. `orelse
    // return null` after the call).  We want the inner call's
    // first..last token.  For a fresh attempt, scan for the
    // FIRST matching node and try several end-token candidates.
    var end = b.rhs_last;
    while (end >= start) : (end -= 1) {
        const name_opt = cache.typeReferenceOfExpr(start, end) catch null;
        if (name_opt) |name| {
            // `name` is the spelling this file dispatches on, so a
            // foreign declaration never collides with a local type of
            // the same leaf name.  Locally declared?  Then the shared
            // two-rung probe answers it; an imported type (`alias.Type`)
            // stays unrefuted so the rule keeps firing.
            if (localTypeHasDeinit(model, name)) |has_deinit| return !has_deinit;
            return false;
        }
        if (end == start) break;
    }
    return false;
}

/// Two-rung local-model deinit probe shared by the ZLS refinement
/// (`rhsTypeViaZlsLacksDeinit`) and the project-wide lookup
/// (`typeHasDeinitProject`): a `types[]` entry first, then the
/// `@This()` file-struct alias.  Null when this file declares
/// neither, so each caller applies its own conservative default to
/// the cross-file / unknown case.
fn localTypeHasDeinit(
    model: *const file_model.FileModel,
    type_name: []const u8,
) ?bool {
    if (model.hasType(type_name)) return model.typeHasMethod(type_name, "deinit");
    if (model.fileIsTypeNamed(type_name)) {
        return model.typeOrFileHasMethod(type_name, "deinit");
    }
    return null;
}

/// True iff `type_name` has a `deinit` method, with cross-file
/// resolution via the FileCache's project-wide @import lookup.
/// Returns true conservatively when the type is unresolvable.
fn typeHasDeinitProject(
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    type_name: []const u8,
) bool {
    if (localTypeHasDeinit(model, type_name)) |has_deinit| return has_deinit;
    // Cross-file: scan @import("./...") declarations.
    if (cache.findTypeAcrossImports(type_name)) |ti| {
        return ti.hasMethod("deinit");
    }
    return true;
}


const CleanupTarget = struct {
    declaration: Ast.TokenIndex,
    field: ?[]const u8 = null,

    fn eql(a: CleanupTarget, b: CleanupTarget) bool {
        if (a.declaration != b.declaration) return false;
        if (a.field) |field| return std.mem.eql(u8, field, b.field orelse return false);
        return b.field == null;
    }
};

fn deferredNodeAt(tree: *const Ast, token: Ast.TokenIndex) ?Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .@"defer" and tag != .@"errdefer") continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) == token) return node;
    }
    return null;
}

fn deferredBody(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    return if (tree.nodeTag(node) == .@"defer")
        tree.nodeData(node).node
    else
        tree.nodeData(node).opt_token_and_node[1];
}

/// A value copy snapshots its initializer. A deferred expression instead
/// reads its receiver when the error leaves the block.
fn valueTarget(
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    evaluated_at: Ast.TokenIndex,
) file_cache_mod.SummaryError!?CleanupTarget {
    const tree = cache.tree;
    const node = cache.nodeForExactSpan(first, last) orelse return null;
    try cache.enterNormalCleanup(node);
    defer cache.leaveNormalCleanup();
    try cache.chargeNormalCleanup(node);
    const tags = tree.tokens.items(.tag);
    if (tags[first] != .identifier) return null;
    const binding = bindings.findAt(tree.tokenSlice(first), first) orelse return null;
    // Reject assignments to THIS declaration, not a same-spelled shadow.
    var t = binding.rhs_last + 1;
    while (t + 1 <= evaluated_at and t + 1 < tags.len) : (t += 1) {
        if (tags[t] != .identifier or tags[t + 1] != .equal) continue;
        if (t > 0 and tags[t - 1] == .period) continue;
        const assigned = bindings.findAt(tree.tokenSlice(t), t) orelse continue;
        if (assigned.name_token == binding.name_token) return null;
    }
    if (last == first + 2 and tags[first + 1] == .period and tags[last] == .identifier)
        return .{ .declaration = binding.name_token, .field = tree.tokenSlice(last) };
    if (first != last) return null;
    if (binding.origin == .alias) {
        return valueTarget(cache, bindings, binding.rhs_first, binding.rhs_last, binding.rhs_last);
    }
    if (binding.origin == .loop_capture and binding.rhs_first < binding.name_token) {
        if (try valueTarget(cache, bindings, binding.rhs_first, binding.rhs_last, binding.rhs_last)) |captured|
            return captured;
    }
    return .{ .declaration = binding.name_token };
}

fn expressionTarget(
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    node: Ast.Node.Index,
    evaluated_at: Ast.TokenIndex,
) file_cache_mod.SummaryError!?CleanupTarget {
    const tree = cache.tree;
    if (tree.nodeTag(node) == .address_of)
        return expressionTarget(cache, bindings, tree.nodeData(node).node, evaluated_at);
    return valueTarget(cache, bindings, tree.firstToken(node), tree.lastToken(node), evaluated_at);
}

fn cleanupMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "close") or std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "deref") or std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "destroy");
}

/// Deliberately small positive witness: direct cleanup, a straight-line
/// block, or an optional payload of the exact owned field. Arbitrary
/// conditional cleanup never supplies an all-error-exits certificate.
fn actionCleans(
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    action: Ast.Node.Index,
    target: CleanupTarget,
    risk: Ast.TokenIndex,
) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    try cache.enterNormalCleanup(action);
    defer cache.leaveNormalCleanup();
    try cache.chargeNormalCleanup(action);
    var block_buffer: [2]Ast.Node.Index = undefined;
    if (tree.blockStatements(&block_buffer, action)) |statements| {
        for (statements) |statement| {
            if (try actionCleans(cache, bindings, statement, target, risk)) return true;
            switch (tree.nodeTag(statement)) {
                .@"return", .@"break", .@"continue" => return false,
                else => {},
            }
            if (!try preservesOrCleans(cache, bindings, statement, target, risk)) return false;
        }
        return false;
    }
    if (tree.fullIf(action)) |branch| {
        if (branch.error_token != null or branch.payload_token == null) return false;
        const held = (try expressionTarget(cache, bindings, branch.ast.cond_expr, risk)) orelse return false;
        if (!CleanupTarget.eql(held, target)) return false;
        return actionCleans(cache, bindings, branch.ast.then_expr, target, risk);
    }
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, action) orelse return false;
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const receiver, const method = tree.nodeData(call.ast.fn_expr).node_and_token;
    const name = tree.tokenSlice(method);
    if (!cleanupMethod(name)) return false;
    const argument_cleanup = std.mem.eql(u8, name, "free") or std.mem.eql(u8, name, "destroy");
    if (argument_cleanup) {
        for (call.ast.params) |argument| {
            const held = (try expressionTarget(cache, bindings, argument, risk)) orelse continue;
            if (CleanupTarget.eql(held, target)) return true;
        }
    } else if (try expressionTarget(cache, bindings, receiver, risk)) |held| {
        if (CleanupTarget.eql(held, target)) return true;
    }
    // A parent destructor is interpreted in its actual declaration/frame.
    // Do not attach a same-named method from an unrelated owner.
    if (target.field == null) return false;
    const held = (try expressionTarget(cache, bindings, receiver, risk)) orelse return false;
    if (held.declaration != target.declaration or held.field != null) return false;
    // Method calls are indexed by the field-access dot, not its member name.
    const query = tree.nodeMainToken(call.ast.fn_expr);
    const canonical = (try cache.actualCallSummaryAt(query, null)) orelse return false;
    if (canonical.callee.tree != tree) return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return false;
    const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return false;
    var parameter_iterator = proto.iterate(tree);
    const self_parameter = parameter_iterator.next() orelse return false;
    const self_name = self_parameter.name_token orelse return false;
    var argument_buffer: [2]Ast.Node.Index = undefined;
    const actual_receiver = (try canonical.callArgumentFor(cache, &argument_buffer, 0)) orelse return false;
    const mapped = (try expressionTarget(cache, bindings, actual_receiver, risk)) orelse return false;
    if (!CleanupTarget.eql(mapped, held)) return false;
    const callee_bindings = (try cache.localBindings(proto, body)).*;
    return actionCleans(cache, &callee_bindings, body, .{
        .declaration = self_name,
        .field = target.field,
    }, tree.lastToken(body));
}

/// A later LIFO action must preserve the selected value or release it
/// before replacing it. Rooted call effects, not unrelated SDK calls,
/// determine whether a selected field can change.
fn preservesOrCleans(
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    action: Ast.Node.Index,
    target: CleanupTarget,
    risk: Ast.TokenIndex,
) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    try cache.enterNormalCleanup(action);
    defer cache.leaveNormalCleanup();
    try cache.chargeNormalCleanup(action);
    if (try actionCleans(cache, bindings, action, target, risk)) return true;
    var buffer: [2]Ast.Node.Index = undefined;
    if (tree.blockStatements(&buffer, action)) |statements| {
        for (statements) |statement| {
            if (try actionCleans(cache, bindings, statement, target, risk)) return true;
            if (!try preservesOrCleans(cache, bindings, statement, target, risk)) return false;
        }
        return true;
    }
    if (tree.fullIf(action)) |branch| {
        if (!try preservesOrCleans(cache, bindings, branch.ast.cond_expr, target, risk)) return false;
        if (!try preservesOrCleans(cache, bindings, branch.ast.then_expr, target, risk)) return false;
        if (branch.ast.else_expr.unwrap()) |other|
            return preservesOrCleans(cache, bindings, other, target, risk);
        return true;
    }
    switch (tree.nodeTag(action)) {
        .assign => {
            const lhs, const rhs = tree.nodeData(action).node_and_node;
            if (try expressionTarget(cache, bindings, lhs, tree.firstToken(action))) |held| {
                if (held.declaration == target.declaration and
                    (held.field == null or CleanupTarget.eql(held, target))) return false;
            }
            return preservesOrCleans(cache, bindings, rhs, target, risk);
        },
        .@"defer", .@"errdefer" => return true, // registration only
        .@"try" => return preservesOrCleans(cache, bindings, tree.nodeData(action).node, target, risk),
        .identifier, .field_access, .number_literal, .string_literal, .enum_literal => return true,
        .simple_var_decl, .aligned_var_decl, .local_var_decl, .global_var_decl => {
            const declaration = tree.fullVarDecl(action).?;
            return preservesOrCleans(cache, bindings, declaration.ast.init_node.unwrap() orelse return true, target, risk);
        },
        else => {},
    }
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, action) orelse {
        // All children are inspected; a conditional cleanup is still
        // not an all-path cleanup certificate.
        var children = @import("type_engine").AstIterator.init(tree, action);
        while (children.next(tree)) |child|
            if (!try preservesOrCleans(cache, bindings, child, target, risk)) return false;
        return true;
    };
    const query = tree.nodeMainToken(call.ast.fn_expr);
    const canonical = (try cache.actualCallSummaryAt(query, null)) orelse {
        // Unknown calls are harmless only when none of their actuals
        // can reach this local owner. Passing it is never safe by default.
        for (call.ast.params) |argument| {
            if (try expressionTarget(cache, bindings, argument, tree.firstToken(action))) |held|
                if (held.declaration == target.declaration) return false;
        }
        if (tree.nodeTag(call.ast.fn_expr) == .field_access) {
            const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
            if (try expressionTarget(cache, bindings, receiver, tree.firstToken(action))) |held|
                if (held.declaration == target.declaration and
                    (held.field == null or CleanupTarget.eql(held, target))) return false;
        }
        return true;
    };
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return false;
    var parameters = proto.iterate(canonical.callee.tree);
    var parameter: u32 = 0;
    while (parameters.next()) |formal| : (parameter += 1) {
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const argument = (try canonical.callArgumentFor(cache, &argument_buffer, parameter)) orelse return false;
        const held = (try expressionTarget(cache, bindings, argument, tree.firstToken(action))) orelse continue;
        if (held.declaration != target.declaration) continue;
        if (held.field != null and !CleanupTarget.eql(held, target)) continue;
        const selected_path = if (held.field == null) target.field orelse "" else "";
        if (try cache.callEffectAt(query, .{ .parameter = .{
            .param = parameter,
            .path = selected_path,
        } }, .{})) |effect| {
            if (effect == .read_only) continue;
        }
        if (canonical.callee.tree != tree) return false;
        const callee_body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return false;
        const callee_bindings = (try cache.localBindings(proto, callee_body)).*;
        if (!try preservesOrCleans(cache, &callee_bindings, callee_body, .{
            .declaration = formal.name_token orelse return false,
            .field = if (held.field == null) target.field else null,
        }, tree.lastToken(callee_body))) return false;
    }
    return true;
}

fn activeCleanup(
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    target: CleanupTarget,
    risk: Ast.TokenIndex,
) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const block: Ast.Node.Index = @enumFromInt(raw);
        const first = tree.firstToken(block);
        if (first < tree.firstToken(body) or first > risk or tree.lastToken(block) < risk) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&buffer, block) orelse continue;
        for (statements, 0..) |statement, index| {
            const registration = tree.firstToken(statement);
            if (registration >= risk) break;
            const tag = tree.nodeTag(statement);
            if (tag != .@"defer" and tag != .@"errdefer") continue;
            if (!try actionCleans(cache, bindings, deferredBody(tree, statement), target, risk)) continue;
            var intact = true;
            for (statements[index + 1 ..]) |later| {
                if (tree.lastToken(later) >= risk) break;
                const later_tag = tree.nodeTag(later);
                const action = if (later_tag == .@"defer" or later_tag == .@"errdefer")
                    deferredBody(tree, later)
                else
                    later;
                if (!try preservesOrCleans(cache, bindings, action, target, risk)) {
                    intact = false;
                    break;
                }
            }
            if (intact) return true;
        }
    }
    return false;
}

fn protectedAt(
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    original: *const local_bindings.Binding,
    risk: Ast.TokenIndex,
) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    const bindings = (try cache.localBindings(proto, body)).*;
    const target: CleanupTarget = .{ .declaration = original.name_token };
    if (try activeCleanup(cache, &bindings, body, target, risk)) return true;
    // Publish only a straight-line store of this precise value before the
    // failing operation. A conditional store is not ownership transfer.
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .assign) continue;
        const assignment: Ast.Node.Index = @enumFromInt(raw);
        const first = tree.firstToken(assignment);
        if (first <= original.rhs_last or first >= risk) continue;
        if (!sameDirectBlock(tree, assignment, risk)) continue;
        const lhs, const rhs = tree.nodeData(assignment).node_and_node;
        const moved = (try expressionTarget(cache, &bindings, rhs, first)) orelse continue;
        if (!CleanupTarget.eql(moved, target)) continue;
        const owner = (try expressionTarget(cache, &bindings, lhs, first)) orelse continue;
        if (owner.field == null) continue;
        // The published slot must still hold the captured value at failure.
        var intact = true;
        for (tree.nodes.items(.tag), 0..) |_, between_raw| {
            const between: Ast.Node.Index = @enumFromInt(between_raw);
            const at = tree.firstToken(between);
            if (at <= tree.lastToken(assignment) or tree.lastToken(between) >= risk) continue;
            if (!sameDirectBlock(tree, between, risk)) continue;
            if (!try preservesOrCleans(cache, &bindings, between, owner, risk)) {
                intact = false;
                break;
            }
        }
        if (!intact) continue;
        if (try activeCleanup(cache, &bindings, body, owner, risk)) return true;
        const root = bindings.findAt(tree.tokenSlice(tree.firstToken(lhs)), first) orelse continue;
        if (root.origin != .param) continue;
        const function = tokens.enclosingFnDecl(tree, first) orelse continue;
        const calls = (try cache.closedLocalCalls(function)) orelse continue;
        if (calls.len == 0) continue;
        var parameters = proto.iterate(tree);
        var parameter: u32 = 0;
        while (parameters.next()) |param| : (parameter += 1) {
            if (param.name_token != root.name_token) continue;
            var all_owned = true;
            for (calls) |call_node| {
                try cache.chargeNormalCleanup(call_node);
                const call_token = tree.firstToken(call_node);
                // Only propagation of this invocation enters the parent's
                // error domain; catch handlers need their own proof.
                if (call_token == 0 or tree.tokenTag(call_token - 1) != .keyword_try) {
                    all_owned = false;
                    break;
                }
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const resolver = cache.zls orelse return false;
                const argument = (try resolver.resolutionFrame().callArgumentIn(&argument_buffer, call_node, parameter)) orelse return false;
                const caller = tokens.enclosingFnDecl(tree, call_token) orelse return false;
                var caller_proto_buffer: [1]Ast.Node.Index = undefined;
                const caller_proto = tokens.fnProto(tree, &caller_proto_buffer, caller) orelse return false;
                const caller_body = tokens.bodyOf(tree, caller) orelse return false;
                const caller_bindings = (try cache.localBindings(caller_proto, caller_body)).*;
                var actual = (try expressionTarget(cache, &caller_bindings, argument, call_token)) orelse return false;
                if (actual.field != null) return false;
                actual.field = owner.field;
                if (!try activeCleanup(cache, &caller_bindings, caller_body, actual, call_token)) {
                    all_owned = false;
                    break;
                }
            }
            if (all_owned) return true;
        }
    }
    return false;
}

fn sameDirectBlock(tree: *const Ast, statement: Ast.Node.Index, risk: Ast.TokenIndex) bool {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const block: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(block) > risk or tree.lastToken(block) < risk) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&buffer, block) orelse continue;
        for (statements) |child| if (child == statement) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    b: TrackedBinding,
) !void {
    const cleanup = if (b.is_fd_open) "close" else "deinit";
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` is bound via `try …`, but a later `try` in this scope has no `errdefer {s}.{s}();` between them — `{s}` leaks every time the next `try` propagates an error",
        .{ b.x_name, b.x_name, cleanup, b.x_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, b.name_token),
        .end = try Pos.fromTokenEnd(tree, b.name_token),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "fromJS binding without errdefer fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const PathLike = struct {
        \\    pub fn fromJS(_: usize, _: usize) !?PathLike { return null; }
        \\    pub fn deinit(_: *PathLike) void {}
        \\};
        \\pub fn rename(ctx: usize, a: usize, b: usize) !struct { o: PathLike, n: PathLike } {
        \\    const old_path = try PathLike.fromJS(ctx, a) orelse return error.Invalid;
        \\    const new_path = try PathLike.fromJS(ctx, b) orelse return error.Invalid;
        \\    return .{ .o = old_path, .n = new_path };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
}

test "errdefer between tries is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const PathLike = struct {
        \\    pub fn fromJS(_: usize, _: usize) !?PathLike { return null; }
        \\    pub fn deinit(_: *PathLike) void {}
        \\};
        \\pub fn rename(ctx: usize, a: usize, b: usize) !struct { o: PathLike, n: PathLike } {
        \\    var old_path = try PathLike.fromJS(ctx, a) orelse return error.Invalid;
        \\    errdefer old_path.deinit();
        \\    var new_path = try PathLike.fromJS(ctx, b) orelse return error.Invalid;
        \\    errdefer new_path.deinit();
        \\    return .{ .o = old_path, .n = new_path };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer X.deref() is also accepted as protection" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Str = struct {
        \\    pub fn fromJS(_: usize, _: usize) !?Str { return null; }
        \\    pub fn deref(_: *const Str) void {}
        \\    pub fn deinit(_: *Str) void {}
        \\};
        \\pub fn parse(ctx: usize, v: usize) !void {
        \\    const str = try Str.fromJS(ctx, v) orelse return error.Invalid;
        \\    defer str.deref();
        \\    _ = try otherFallible();
        \\}
        \\fn otherFallible() !void {}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "lowercase receiver (gpa.dupe) doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn foo(a: std.mem.Allocator) !void {
        \\    const buf = try a.dupe(u8, "abc");
        \\    defer a.free(buf);
        \\    _ = try otherFallible();
        \\}
        \\fn otherFallible() !void {}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "file-handle open (createFile/openFile) without errdefer fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn writeAof(dir: std.fs.Dir, path: []const u8) !void {
        \\    const file = try dir.createFile(path, .{});
        \\    try file.sync();
        \\    file.close();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
}

test "file open with errdefer file.close() is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn writeAof(dir: std.fs.Dir, path: []const u8) !void {
        \\    const file = try dir.createFile(path, .{});
        \\    errdefer file.close();
        \\    try file.sync();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "if-let capture: binding scope ends at body brace; outer try doesn't fire" {
    // `if (try Type.fromJS(...)) |x| { ... }` — `x`'s scope is the
    // if-body braces.  A try AFTER the closing `}` is in an unrelated
    // scope; the binding is already gone, no leak possible.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Target = struct {
        \\    pub fn fromJS(_: i32) ?Target { return .{}; }
        \\    pub fn deinit(_: *Target) void {}
        \\};
        \\fn other() !void {}
        \\pub fn caller(g: i32) !void {
        \\    if (try Target.fromJS(g)) |t| {
        \\        _ = t;
        \\    }
        \\    try other();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "if-let capture: try INSIDE the body without errdefer still fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Target = struct {
        \\    pub fn fromJS(_: i32) ?Target { return .{}; }
        \\    pub fn deinit(_: *Target) void {}
        \\};
        \\fn other() !void {}
        \\pub fn caller(g: i32) !void {
        \\    if (try Target.fromJS(g)) |t| {
        \\        _ = t;
        \\        try other();
        \\    }
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
}

test "binding in `brk:` block: outer try doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct {
        \\    pub fn fromJS(_: i32) ?T { return .{}; }
        \\    pub fn deinit(_: *T) void {}
        \\};
        \\fn other() !void {}
        \\pub fn caller(g: i32) !void {
        \\    const v = brk: {
        \\        if (try T.fromJS(g)) |inner| {
        \\            break :brk inner;
        \\        }
        \\        break :brk T{};
        \\    };
        \\    _ = v;
        \\    try other();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "non-fromJS method doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct {
        \\    pub fn create() !T { return .{}; }
        \\    pub fn deinit(_: *T) void {}
        \\};
        \\pub fn foo() !void {
        \\    const x = try T.create();
        \\    _ = x;
        \\    _ = try otherFallible();
        \\}
        \\fn otherFallible() !void {}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

/// Run the rule over `main_source` with `remote.zig` (holding
/// `remote_source`) importable beside it, and return how many problems
/// it reported.  Both files are real so the type engine can follow the
/// import.
fn reportsWithRemote(remote_source: []const u8, main_source: []const u8) !usize {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    const type_engine = @import("type_engine");
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "remote.zig", .data = remote_source });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const main_source_z = try gpa.dupeZ(u8, main_source);
    defer gpa.free(main_source_z);
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: type_engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, main_source_z);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    cache.setZls(&resolver);
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    for (problems.items) |problem| try std.testing.expectEqualStrings(R, problem.rule_id);
    return problems.items.len;
}

test "imported type that has deinit is not judged by a same-named local type without one" {
    // `Alias.fromJS` returns `remote.Foo`, which owns resources.  The
    // local `Foo` is an unrelated type of the same leaf name and has no
    // `deinit`; its leaf name must not refute the imported type.
    try std.testing.expectEqual(@as(usize, 1), try reportsWithRemote(
        \\pub const Foo = struct {
        \\    pub fn fromJS(_: usize) !Foo { return .{}; }
        \\    pub fn deinit(_: *Foo) void {}
        \\};
    ,
        \\const remote = @import("remote.zig");
        \\const Foo = struct {
        \\    pub fn fromJS(_: usize) !Foo { return .{}; }
        \\};
        \\const Alias = remote.Foo;
        \\fn later() !void { return error.Later; }
        \\pub fn open() !void {
        \\    const x = try Alias.fromJS(1);
        \\    _ = x;
        \\    try later();
        \\}
    ));
}

test "imported type without deinit is not judged by a same-named local type with one" {
    // The local `Foo` has a `deinit` and the imported `remote.Foo` has
    // none.  The imported type is a different declaration: the local
    // `deinit` is not credited to it, and a foreign declaration stays
    // unrefuted, so the rule still reports the unprotected `try`.
    try std.testing.expectEqual(@as(usize, 1), try reportsWithRemote(
        \\pub const Foo = struct {
        \\    pub fn fromJS(_: usize) !Foo { return .{}; }
        \\};
    ,
        \\const remote = @import("remote.zig");
        \\const Foo = struct {
        \\    pub fn fromJS(_: usize) !Foo { return .{}; }
        \\    pub fn deinit(_: *Foo) void {}
        \\};
        \\fn later() !void { return error.Later; }
        \\pub fn open() !void {
        \\    const x = try remote.Foo.fromJS(1);
        \\    _ = x;
        \\    try later();
        \\}
    ));
}

test "missing-errdefer-between-tries: moved local has active cleanup" {
    try testing.expectNoFire(check,
        \\fn f(dir: anytype) !void {
        \\    const opened = try dir.openFile("x", .{});
        \\    var handle = opened;
        \\    defer handle.close();
        \\    try later();
        \\}
        \\fn later() !void {}
    );
}

test "missing-errdefer-between-tries: cleanup value binding and error domains" {
    const prefix =
        \\const File = struct { fn close(_: File) void {} };
        \\const Dir = struct { fn openFile(_: Dir, _: []const u8, _: anytype) !File { return .{}; } };
        \\fn later() !void {}
    ;
    const cases = .{
        .{ @as(usize, 1),
            \\fn f(dir: Dir, other: File) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    var handle = opened;
            \\    defer handle.close();
            \\    handle = other;
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir, yes: bool) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    if (yes) { defer opened.close(); }
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir, other: File) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    { const opened = other; defer opened.close(); }
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    defer { _ = opened; }
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    defer { var copy = opened; copy = .{}; copy.close(); }
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    try later();
            \\    defer opened.close();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir, yes: bool) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    errdefer { if (yes) opened.close(); }
            \\    try later();
            \\}
        },
        .{ @as(usize, 0),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    errdefer |err| { _ = err; opened.close(); }
            \\    try later();
            \\}
        },
        .{ @as(usize, 0),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    defer { var copy = opened; copy.close(); }
            \\    try later();
            \\}
        },
        .{ @as(usize, 0),
            \\fn f(dir: Dir, other: File) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    var handle = opened;
            \\    const saved = handle;
            \\    handle = other;
            \\    defer saved.close();
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    var handle = opened;
            \\    defer handle.close();
            \\    errdefer { handle = .{}; }
            \\    try later();
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    try inspect(opened);
            \\}
            \\fn inspect(_: File) !void {}
        },
        .{ @as(usize, 0),
            \\fn f(dir: Dir) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    const maybe: ?File = opened;
            \\    if (maybe) |held| { defer held.close(); try later(); }
            \\}
        },
        .{ @as(usize, 1),
            \\fn f(dir: Dir, other: File) !void {
            \\    const opened = try dir.openFile("x", .{});
            \\    const maybe: ?File = other;
            \\    if (maybe) |held| { defer held.close(); try later(); }
            \\}
        },
    };
    inline for (cases) |case| {
        var problems = try testing.runRule(std.testing.allocator, check, prefix ++ "\n" ++ case[1]);
        defer freeProblems(std.testing.allocator, &problems);
        try std.testing.expectEqual(case[0], problems.items.len);
    }
}

test "missing-errdefer-between-tries: closed caller owns published optional field" {
    const prefix =
        \\const File = struct { fn close(_: File) void {} };
        \\const Dir = struct { fn openDir(_: Dir, _: []const u8, _: anytype) !File { return .{}; } };
        \\const Owner = struct {
        \\    dir: Dir,
        \\    slot: ?File = null,
        \\    fn close(self: *Owner) void {
        \\        if (self.slot) |held| { held.close(); self.slot = null; }
        \\    }
        \\};
        \\fn later() !void {}
        \\fn fill(owner: *Owner) !void {
        \\    const opened = try owner.dir.openDir("raw", .{});
        \\    owner.slot = opened;
        \\    try later();
        \\}
    ;
    const cases = .{
        .{ @as(usize, 0),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    defer owner.close();
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 0),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    errdefer owner.close();
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 0),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    defer owner.close();
            \\    defer if (owner.slot) |held| { held.close(); owner.slot = null; };
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 1),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    defer owner.close();
            \\    errdefer { owner.slot = null; }
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 1),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    errdefer owner.close();
            \\    fill(&owner) catch {};
            \\}
        },
        .{ @as(usize, 1),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    var other: Owner = .{ .dir = .{} };
            \\    defer other.close();
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 1),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 1),
            \\pub fn root(yes: bool) !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    if (yes) { defer owner.close(); }
            \\    try fill(&owner);
            \\}
        },
        .{ @as(usize, 1),
            \\pub fn root() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    defer owner.close();
            \\    try fill(&owner);
            \\}
            \\pub fn unowned() !void {
            \\    var owner: Owner = .{ .dir = .{} };
            \\    try fill(&owner);
            \\}
        },
    };
    inline for (cases) |case| {
        var problems = try testing.runRuleTyped(std.testing.allocator, check, prefix ++ "\n" ++ case[1]);
        defer freeProblems(std.testing.allocator, &problems);
        try std.testing.expectEqual(case[0], problems.items.len);
    }
}

test "missing-errdefer-between-tries: published value cannot change slots before failure" {
    const prefix =
        \\const File = struct { fn close(_: File) void {} };
        \\const Dir = struct { fn openDir(_: Dir, _: []const u8, _: anytype) !File { return .{}; } };
        \\const Owner = struct {
        \\    dir: Dir,
        \\    slot: ?File = null,
        \\    other: ?File = null,
        \\    fn close(self: *Owner) void { if (self.slot) |held| held.close(); }
        \\};
        \\fn later() !void {}
        \\pub fn root() !void {
        \\    var owner: Owner = .{ .dir = .{} };
        \\    defer owner.close();
        \\    try fill(&owner);
        \\}
    ;
    const cases = .{
        \\fn fill(owner: *Owner) !void {
        \\    const opened = try owner.dir.openDir("raw", .{});
        \\    owner.slot = opened;
        \\    owner.slot = null;
        \\    try later();
        \\}
        ,
        \\fn fill(owner: *Owner) !void {
        \\    const opened = try owner.dir.openDir("raw", .{});
        \\    owner.other = opened;
        \\    try later();
        \\}
        ,
    };
    inline for (cases) |source| {
        var problems = try testing.runRuleTyped(std.testing.allocator, check, prefix ++ "\n" ++ source);
        defer freeProblems(std.testing.allocator, &problems);
        try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    }
}

test "missing-errdefer-between-tries: SDK published directory keeps canonical LIFO owner" {
    // Result.zig:586 publishes rawdir before allocation. Its caller registers
    // close before conditional discard; discard must release or preserve rawdir.
    const prefix =
        \\const std = @import("std");
        \\const Backing = struct {
        \\    dir: std.Io.Dir,
        \\    raw_open: ?std.Io.Dir = null,
        \\    other: ?std.Io.Dir = null,
    ;
    const close =
        \\    fn close(self: *Backing, io: std.Io) void {
        \\        if (self.raw_open) |dir| {
        \\            dir.close(io);
        \\            self.raw_open = null;
        \\        }
        \\        self.dir.close(io);
        \\    }
    ;
    const suffix =
        \\};
        \\fn buildBundle(allocator: std.mem.Allocator, io: std.Io, backing: *Backing) !void {
        \\    const rawdir = try backing.dir.openDir(io, "raw", .{
        \\        .iterate = true,
        \\        .follow_symlinks = false,
        \\    });
        \\    backing.raw_open = rawdir;
        \\    const entries = try allocator.alloc(u8, 2);
        \\    defer allocator.free(entries);
        \\}
        \\pub fn publish(allocator: std.mem.Allocator, io: std.Io, dir: std.Io.Dir, retain: bool) !void {
        \\    var backing: Backing = .{ .dir = dir };
        \\    defer backing.close(io);
        \\    defer if (!retain) backing.discard(io);
        \\    try buildBundle(allocator, io, &backing);
        \\}
    ;
    const cases = .{
        .{ @as(usize, 0), close,
            \\    fn discard(self: *Backing, io: std.Io) void {
            \\        if (self.raw_open) |dir| {
            \\            dir.close(io);
            \\            self.raw_open = null;
            \\        }
            \\    }
        },
        .{ @as(usize, 1), close,
            \\    fn discard(self: *Backing, io: std.Io) void {
            \\        _ = io;
            \\        self.raw_open = null;
            \\    }
        },
        .{ @as(usize, 1),
            \\    fn close(self: *Backing, io: std.Io) void {
            \\        if (self.other) |dir| dir.close(io);
            \\        self.dir.close(io);
            \\    }
            ,
            \\    fn discard(_: *Backing, _: std.Io) void {}
        },
        .{ @as(usize, 1),
            \\    fn close(self: *Backing, io: std.Io) void {
            \\        _ = self.raw_open;
            \\        self.dir.close(io);
            \\    }
            ,
            \\    fn discard(_: *Backing, _: std.Io) void {}
        },
        .{ @as(usize, 0), close,
            \\    fn discard(self: *Backing, io: std.Io) void {
            \\        _ = io;
            \\        self.other = null;
            \\    }
        },
    };
    inline for (cases) |case| {
        const source = prefix ++ "\n" ++ case[1] ++ "\n" ++ case[2] ++ "\n" ++ suffix;
        var problems = try testing.runRuleTyped(std.testing.allocator, check, source);
        defer freeProblems(std.testing.allocator, &problems);
        try std.testing.expectEqual(case[0], problems.items.len);
    }
}
