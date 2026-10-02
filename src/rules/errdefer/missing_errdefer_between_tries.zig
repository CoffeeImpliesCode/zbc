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
//!   3. From each binding, scan forward for the next `try`.  If a
//!      `defer`/`errdefer` referencing X appears between, protected.
//!      Otherwise fire.

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

    const bindings = try cache.localBindings(proto, body);

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
        if (rhsArenaIsDeferDeinited(tree, b.rhs_first, b.rhs_last, first, last)) continue;

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
            // FD wrapped into a helper struct with defer cleanup:
            // `const fd = try sys.openat(...); const file = sys.File{
            // .handle = fd }; defer file.close();` — the wrapper
            // owns the fd's lifetime via its own defer.  Skip.
            if (fdWrappedAndDeferred(tree, tags, b, last)) continue;
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
                    if (cleanupReferencesLocal(tree, u, b.x_name, last)) {
                        has_cleanup = true;
                        break;
                    }
                },
                .keyword_try => {
                    found_try = true;
                    // Consumption-by-call skip: if the next `try`'s
                    // call passes `<x_name>` (or `&<x_name>`) as an
                    // arg, the call is the consumer.  The bound
                    // resource is transferred into the called fn's
                    // ownership; success or failure of the call is
                    // the resource's transition point, not a leak
                    // window the caller must defend.
                    if (nextCallPassesArg(tree, tags, u, last, b.x_name)) {
                        has_cleanup = true;
                    }
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

/// True iff the `try` at `try_tok` is followed by a CALL whose
/// argument list mentions `<arg_name>` as a bare identifier
/// (\`name\` or `&name`).  Walks the source from the next `(`
/// matching paren-depth to find the call's args, then scans for
/// the identifier with a word-boundary check.
fn nextCallPassesArg(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    try_tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
    arg_name: []const u8,
) bool {
    // Find the first `(` after the try (within the next ~50 tokens).
    var p: Ast.TokenIndex = try_tok + 1;
    const scan_lim: Ast.TokenIndex = if (try_tok + 50 < last) try_tok + 50 else last;
    while (p <= scan_lim and tags[p] != .l_paren) : (p += 1) {}
    if (p > scan_lim or tags[p] != .l_paren) return false;
    const close = tokens.matchParen(tags, p, last) orelse return false;
    var k: Ast.TokenIndex = p + 1;
    while (k < close) : (k += 1) {
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), arg_name)) continue;
        // Word-boundary check: no preceding `.` (field access) and
        // not part of a longer identifier (already implied by .identifier).
        if (k > 0 and tags[k - 1] == .period) continue;
        return true;
    }
    return false;
}

const ParsedCall = struct {
    type_name: []const u8,
    method: []const u8,
};

/// Walk forward through an `<ident>(.<ident>)*(...)` chain starting
/// at `start`.  Returns (type_name, method) where `method` is the
/// LAST identifier before the first `(`, and `type_name` is the
/// one immediately before it.  Returns null when the chain isn't
/// at least `<Type>.<method>(`.
/// Detect `<arena>.allocator()` in the binding's RHS where `<arena>`
/// has a `defer <arena>.deinit(...)` in the fn body.  Used to skip
/// the rule on arena-rooted bindings — the arena's defer handles
/// cleanup on every return (success or error), so an errdefer for
/// the binding itself is redundant.
fn rhsArenaIsDeferDeinited(
    tree: *const Ast,
    rhs_first: Ast.TokenIndex,
    rhs_last: Ast.TokenIndex,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    // Scan the RHS for `<ident> . allocator (` patterns and collect
    // the receiver names.
    var t: Ast.TokenIndex = rhs_first;
    while (t + 3 <= rhs_last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "allocator")) continue;
        if (tags[t + 3] != .l_paren) continue;
        // Walking back to ensure this isn't `something.<ident>.allocator()` —
        // we want the bare `<arena_name>.allocator()` receiver.  An
        // immediately-preceding `.` means it's a chained access; the
        // arena name is whatever the chain root is, but the canonical
        // pattern uses a plain local, so be conservative.
        if (t > rhs_first and tags[t - 1] == .period) continue;
        const arena_name = tree.tokenSlice(t);
        if (deferDeinitOf(tree, arena_name, body_first, body_last)) return true;
    }
    return false;
}

/// True iff the fn body contains `defer <arena_name>.deinit(` anywhere.
fn deferDeinitOf(
    tree: *const Ast,
    arena_name: []const u8,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    var u: Ast.TokenIndex = body_first;
    while (u + 4 <= body_last) : (u += 1) {
        if (tags[u] != .keyword_defer) continue;
        if (tags[u + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(u + 1), arena_name)) continue;
        if (tags[u + 2] != .period) continue;
        if (tags[u + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(u + 3), "deinit")) continue;
        if (u + 4 <= body_last and tags[u + 4] == .l_paren) return true;
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

/// True iff `Type` has a `deinit` method discoverable in the
/// FileModel.  Conservative: cross-file / unknown types pass through
/// (true) so we don't miss real bugs whose types are declared in
/// another file.  Returns false only when the type IS in the local
/// file AND demonstrably has no `deinit`.
/// Detect the FD-wrap-with-defer-cleanup pattern: the fd binding
/// is immediately consumed into a helper struct's `.handle = <fd>`
/// field, and that helper has a `defer <helper>.close();` (or
/// `.deinit()`) within the same scope.  The wrapper takes
/// ownership of the fd; cleanup flows through the wrapper.
fn fdWrappedAndDeferred(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    b: anytype,
    body_last: Ast.TokenIndex,
) bool {
    // Scan forward from the binding's terminating `;` for a
    // `<wrapper> = <SomeType>{ .handle = <name> }` shape — find
    // the wrapper local name.  Bound to K=30 tokens for cheapness.
    var t: Ast.TokenIndex = b.rhs_last + 1;
    var i: u32 = 0;
    while (t + 6 < body_last and i < 30) : ({
        t += 1;
        i += 1;
    }) {
        // Pattern: `const <wrapper> = <TypeRef>{ .handle = <name>, ... };`
        if (tags[t] != .keyword_const and tags[t] != .keyword_var) continue;
        if (t + 1 >= body_last or tags[t + 1] != .identifier) continue;
        const wrapper_name = tree.tokenSlice(t + 1);
        // Walk forward for `.handle = <b.name>` within the struct
        // literal.  Bound by `;`.
        var u: Ast.TokenIndex = t + 2;
        while (u + 4 <= body_last and tags[u] != .semicolon) : (u += 1) {
            if (tags[u] != .period) continue;
            if (tags[u + 1] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(u + 1), "handle")) continue;
            if (tags[u + 2] != .equal) continue;
            if (tags[u + 3] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(u + 3), b.name)) continue;
            // Found the wrap.  Now look for a defer on the wrapper
            // within the remaining body.
            if (deferCleanupOn(tree, tags, wrapper_name, u, body_last)) return true;
        }
    }
    return false;
}

fn deferCleanupOn(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    name: []const u8,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var u: Ast.TokenIndex = start;
    while (u + 4 <= end) : (u += 1) {
        if (tags[u] != .keyword_defer and tags[u] != .keyword_errdefer) continue;
        if (tags[u + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(u + 1), name)) continue;
        if (tags[u + 2] != .period) continue;
        if (tags[u + 3] != .identifier) continue;
        const m = tree.tokenSlice(u + 3);
        if (std.mem.eql(u8, m, "close") or std.mem.eql(u8, m, "deinit")) return true;
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
            if (model.hasType(name)) {
                if (!model.typeHasMethod(name, "deinit")) return true;
                return false;
            }
            if (model.fileIsTypeNamed(name)) {
                return !model.typeOrFileHasMethod(name, "deinit");
            }
            // Resolved to a cross-file type name we can't refute.
            return false;
        }
        if (end == start) break;
    }
    return false;
}

/// True iff `type_name` has a `deinit` method, with cross-file
/// resolution via the FileCache's project-wide @import lookup.
/// Returns true conservatively when the type is unresolvable.
fn typeHasDeinitProject(
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    type_name: []const u8,
) bool {
    if (model.hasType(type_name)) {
        return model.typeHasMethod(type_name, "deinit");
    }
    if (model.fileIsTypeNamed(type_name)) {
        return model.typeOrFileHasMethod(type_name, "deinit");
    }
    if (cache.findTypeAcrossImports(type_name)) |resolved| {
        return resolved.info.hasMethod("deinit");
    }
    return true;
}

/// True iff the `defer` / `errdefer` at `kw` mentions `x_name` in
/// its (inline or block) body.  Any mention is treated as cleanup
/// — covers receiver form (`X.cleanup()`) AND arg form
/// (`self.close_socket(X)`, `alloc.free(X)`).
fn cleanupReferencesLocal(tree: *const Ast, kw: Ast.TokenIndex, x_name: []const u8, last: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (kw + 1 > last) return false;
    // Inline form: scan until the next `;` at depth 0.
    if (tags[kw + 1] != .l_brace and tags[kw + 1] != .pipe) {
        var paren: u32 = 0;
        var t: Ast.TokenIndex = kw + 1;
        while (t <= last) : (t += 1) {
            switch (tags[t]) {
                .l_paren => paren += 1,
                .r_paren => if (paren > 0) {
                    paren -= 1;
                },
                .semicolon => if (paren == 0) break,
                .identifier => if (std.mem.eql(u8, tree.tokenSlice(t), x_name)) return true,
                else => {},
            }
        }
        return false;
    }
    // Optional capture (errdefer only): `errdefer |err| { … }`.
    var scan_start: Ast.TokenIndex = kw + 1;
    if (tags[scan_start] == .pipe) {
        scan_start += 1;
        while (scan_start <= last and tags[scan_start] != .pipe) : (scan_start += 1) {}
        if (scan_start > last) return false;
        scan_start += 1;
    }
    if (scan_start > last or tags[scan_start] != .l_brace) return false;
    var depth: u32 = 1;
    var t: Ast.TokenIndex = scan_start + 1;
    while (t <= last and depth > 0) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => {
                depth -= 1;
                if (depth == 0) break;
            },
            .identifier => if (std.mem.eql(u8, tree.tokenSlice(t), x_name)) return true,
            else => {},
        }
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
        .start = Pos.fromTokenStart(tree, b.name_token),
        .end = Pos.fromTokenEnd(tree, b.name_token),
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
