//! Missing-deinit-on-composed-owner detector — a struct `Outer`
//! has a `deinit` method.  One of its value-typed fields has a
//! TYPE that's a struct in the SAME FILE also exposing a cleanup
//! method (`deinit` / `close` / `destroy` / `free` / `stop` /
//! `finalize` / `dispose`).  But `Outer.deinit` doesn't call
//! `<self>.<field>.<cleanup>(...)` — the inner's destructor is
//! never invoked, so the inner's owned non-memory resources (file
//! handles, sockets, mmaps, refs) leak.
//!
//! Real-world: ziglang/zig#22683 (`StackIterator.deinit` forgot
//! `it.ma.deinit()` → `/proc/self/mem` leaked).  Same family as
//! ziglang/zig#20192 (intermediate `Dir` leaked) and
//! ziglang/zig#18651 (Thread.Pool init cleanup gap).
//!
//! Rewritten via the AST-level model_query DSL.

const std = @import("std");
const Ast = std.zig.Ast;

const file_model = @import("../../model/file_model.zig");
const mq = @import("../../model/model_query.zig");
const tokens = @import("../../ast/tokens.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");
const fn_summary = @import("../../model/fn_summary.zig");
const TypeResolver = @import("../../type_resolver.zig").TypeResolver;

const R = "missing-deinit-on-composed-owner";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    if (!config_mod.isEnabled(config, .missing_deinit_on_composed_owner)) return;

    const model = try cache.fileModel();

    // Find all structs that have a `deinit` method.
    const outers = try mq.findTypes(gpa, model, .{
        .kind = .struct_,
        .has_method = .{ .name_eq = "deinit" },
    });
    defer gpa.free(outers);

    for (outers) |outer| {
        const deinit = outer.findMethod("deinit").?;

        // Find this struct's value-typed fields whose declared type
        // is a struct in this file that exposes a cleanup method.
        const fields = try mq.findFields(gpa, model, tree, outer, .{
            .value_typed = true,
            .type_matches = .{ .has_method = .{ .name_pred = isCleanupName } },
        });
        defer gpa.free(fields);

        for (fields) |field| {
            // Refcount-machinery field: e.g. `ref_count: Route.RefCount`
            // where RefCount comes from `bun.ptr.RefCount(@This(), ...)`.
            // The field IS the refcount; cleanup happens via the
            // outer's ref/deref methods, not direct field deinit.
            // Check the LAST identifier of the declared type chain —
            // resolveFieldType returns the FIRST-identifier's type info
            // (e.g. "Route" for `Route.RefCount`), but the suffix
            // signal lives at the chain's tail.
            if (fieldTypeTrailingNameEndsWith(tree, field, "RefCount")) continue;
            // Optional-null-default skip: `<field>: ?T = null` only
            // holds a non-null T when something explicitly assigned
            // it.  An outer deinit that doesn't touch the field
            // doesn't leak when the field stays null (the common
            // case for "lazy/optional sub-state").  The
            // overwrite-without-deinit rule covers the case where
            // someone DOES assign to the field without prior cleanup.
            if (model.fieldIsOptionalNullDefault(outer.qualified_name, field.name)) continue;
            const inner_ti = mq.resolveFieldTypeScoped(tree, model, outer, field) orelse continue;

            // Static cleanup-named functions (for example allocator
            // vtable callbacks taking `ctx: *anyopaque`) are not
            // destructors for the containing type. Require a
            // model-recognized receiver.
            if (!anyNonTrivialReceiverCleanup(tree, inner_ti)) continue;

            // Refcounted-inner skip: when the inner type uses
            // `bun.ptr.RefCount(@This(), ...)` machinery, its
            // `deinit` is *private*, invoked automatically by the
            // last `.deref()`.  Outer types must NOT call
            // `<self>.<field>.deinit()` directly — they should call
            // `.deref()` instead.  Our rule's prescription is
            // wrong for refcounted innerss; skip.
            if (innerIsRefCounted(tree, inner_ti)) continue;

            if (try bodyCallsFieldDestructor(cache, model, outer, inner_ti, deinit.fn_decl, 0, field.name, null, null)) continue;

            // Optional-unwrap: `if (X.field) |*?cap| { ... cap.<cleanup>(...); ... }`.
            // The user explicitly handled the optional and called
            // cleanup on the unwrapped capture — no leak.
            if (bodyHandlesFieldViaUnwrap(tree, deinit, field.name, inner_ti)) continue;


            // Circular-ownership skip: when the inner's `deinit`
            // body navigates back to the outer via
            // `@fieldParentPtr("<field>", self)` and calls the
            // outer's `destroy`/`deinit`, the cleanup is intended
            // to be invoked from OUTSIDE the outer's deinit chain
            // (calling it from inside would recurse).  The inner
            // is a view embedded in the outer's allocation; no
            // separate cleanup is needed when the outer is freed.
            if (innerDeinitUsesFieldParentPtr(tree, inner_ti, field.name)) continue;

            // Caller-supplied field skip: if the type's `init` /
            // `create` method takes a parameter whose name matches
            // the field, the value is owned by the caller and only
            // BORROWED into the struct.  The outer's deinit
            // legitimately leaves cleanup to the caller.  Common
            // in Bun's container types (e.g. `Entry.promise: Promise`
            // initialised from `create(allocator, command, promise)`).
            if (fieldIsCallerSupplied(tree, outer, field.name)) continue;

            // File-as-struct borrow skip: when the field's type IS the
            // file's root struct (`const T = @This()`), any nested
            // struct holding a VALUE of type T is borrowing the file's
            // primary resource, not owning it.  The file manages its
            // own lifetime; the nested struct is a view/slice of it.
            if (model.fileIsTypeNamed(inner_ti.name)) continue;


            try report(gpa, problems, tree, field.name_token, field.name, inner_ti.name);
        }
    }
}

/// True iff `ti` has a non-trivial cleanup method that is modeled
/// as an instance method. A static `free(ctx, bytes)` callback is an
/// allocator interface function, not a composed value destructor.
fn anyNonTrivialReceiverCleanup(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    for (ti.methods) |m| {
        if (m.receiver == null or !method_names.isCleanupMethodName(m.name)) continue;
        if (!tokens.isTrivialBody(tree, m.body_first, m.body_last)) return true;
    }
    return false;
}

const CleanupFrame = struct {
    declaration: Ast.Node.Index,
    parent: ?*const CleanupFrame,
};

/// Follow the exact receiver/formal mapping through teardown wrappers. A field
/// mention, an unrelated receiver, or a cleanup elsewhere in the lifecycle is
/// not evidence that this destructor invokes the field's destructor.
fn bodyCallsFieldDestructor(
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    outer: *const file_model.TypeInfo,
    inner: *const file_model.TypeInfo,
    declaration: Ast.Node.Index,
    parameter: u32,
    field_name: []const u8,
    frame: ?TypeResolver.ResolutionFrame,
    parent: ?*const CleanupFrame,
) file_cache_mod.SummaryError!bool {
    var ancestor = parent;
    while (ancestor) |visited| : (ancestor = visited.parent) {
        if (visited.declaration == declaration) return false;
    }
    const visit = CleanupFrame{ .declaration = declaration, .parent = parent };
    const tree = model.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    const bindings = (try cache.localBindings(proto, body)).*;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    try cache.enterNormalCleanup(declaration);
    defer cache.leaveNormalCleanup();
    var arena = std.heap.ArenaAllocator.init(cache.gpa);
    defer arena.deinit();
    const index = try cache.getCallIndex();
    // Calls are indexed once. No token spelling can create a call that is not
    // present in the AST, and nested declarations cannot supply a wrapper edge.
    var calls = index.by_callee_token.iterator();
    while (calls.next()) |entry| {
        const node = entry.value_ptr.*;
        const token = entry.key_ptr.*;
        if (token <= tree.firstToken(body) or token >= tree.lastToken(body)) continue;
        if (!callIsUnconditional(tree, body, node, proto, parameter)) continue;
        try cache.chargeNormalCleanup(node);
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, node) orelse continue;
        const canonical = if (cache.zls != null)
            try cache.actualCallSummaryAt(token, frame)
        else
            null;
        if (tree.nodeTag(call.ast.fn_expr) == .field_access) {
            const access = tree.nodeData(call.ast.fn_expr).node_and_token;
            const method = inner.findMethod(tree.tokenSlice(access[1]));
            if (method) |cleanup| {
                if (cleanup.receiver != null and isCleanupName(cleanup.name)) {
                    const receiver = access[0];
                    const owner = try fn_summary.ownerOfExpr(arena.allocator(), tree, proto, &bindings,
                        tree.firstToken(receiver), tree.lastToken(receiver), 0);
                    if (owner == .param and owner.param.param == parameter and
                        std.mem.eql(u8, owner.param.path, field_name))
                    {
                        if (canonical) |actual| {
                            if (actual.callee.tree == tree and actual.callee.declaration == cleanup.fn_decl) return true;
                        } else if (cache.zls == null and declaration == outer.findMethod("deinit").?.fn_decl) {
                            return true;
                        }
                    }
                }
            }
        }
        const actual = canonical orelse continue;
        if (actual.callee.tree != tree or actual.callee.declaration == declaration) continue;
        var callee_buffer: [1]Ast.Node.Index = undefined;
        const callee_proto = tokens.fnProto(tree, &callee_buffer, actual.callee.declaration) orelse continue;
        var parameters = callee_proto.iterate(tree);
        var position: u32 = 0;
        while (parameters.next()) |_| : (position += 1) {
            var arguments: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(cache, &arguments, position)) orelse continue;
            const owner = try fn_summary.ownerOfExpr(arena.allocator(), tree, proto, &bindings,
                tree.firstToken(argument), tree.lastToken(argument), 0);
            if (owner != .param or owner.param.param != parameter or owner.param.path.len != 0) continue;
            const resolver = cache.zls orelse continue;
            if (try bodyCallsFieldDestructor(cache, model, outer, inner, actual.callee.declaration,
                position, field_name, resolver.frameForFunction(actual.callee.reference), &visit)) return true;
        }
    }
    return false;
}

/// Only top-level sequencing can prove the wrapper obligation here. Conditional
/// cleanup, early successful returns and reset-before-cleanup remain unknown.
fn callIsUnconditional(tree: *const Ast, body: Ast.Node.Index, call: Ast.Node.Index, proto: Ast.full.FnProto, parameter: u32) bool {
    const tags = tree.tokens.items(.tag);
    const target = tree.firstToken(call);
    var parameters = proto.iterate(tree);
    var position: u32 = 0;
    var receiver: ?[]const u8 = null;
    while (parameters.next()) |p| : (position += 1) {
        if (position == parameter) receiver = tree.tokenSlice(p.name_token orelse return false);
    }
    const name = receiver orelse return false;
    var depth: usize = 0;
    var t = tree.firstToken(body);
    while (t < target) : (t += 1) {
        if (tags[t] == .l_brace) depth += 1;
        if (tags[t] == .r_brace) depth -= 1;
        if (tags[t] == .keyword_return and tags[t + 1] != .keyword_error) {
            const end = tokens.findStmtSemicolon(tags, t + 1, tree.lastToken(body)) orelse return false;
            if (end < target) return false;
        }
        if (tags[t] == .identifier and std.mem.eql(u8, tree.tokenSlice(t), name) and
            t + 2 < target and tags[t + 1] == .period_asterisk and tags[t + 2] == .equal) return false;
    }
    if (depth != 1) return false;
    var previous = target;
    while (previous > tree.firstToken(body)) {
        previous -= 1;
        if (tags[previous] == .keyword_try or tags[previous] == .keyword_return) continue;
        return tags[previous] == .semicolon or tags[previous] == .l_brace or tags[previous] == .r_brace;
    }
    return false;
}


/// True iff `inner_ti` is a refcounted type — its `deinit` is meant
/// to be invoked only by the refcount machinery on the last
/// `.deref()`, never by an outer's deinit directly.  Detection:
/// the type has a `ref_count` field whose declared type expression
/// contains `RefCount(@This(),` — the canonical bun shape produced
/// by `bun.ptr.RefCount(@This(), "ref_count", deinit, ...)`.
fn innerIsRefCounted(tree: *const Ast, inner_ti: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    // Look anywhere in the type's body for the canonical bun shape:
    //   `RefCount(@This(), ...)` — typically the RHS of a
    //   `const RefCount = bun.ptr.RefCount(@This(), "ref_count", deinit, .{});`
    //   decl, but matching the call shape directly is robust against
    //   whatever local alias name the type uses.
    var t: Ast.TokenIndex = inner_ti.body_first;
    while (t + 3 <= inner_ti.body_last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "RefCount")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "@This")) continue;
        return true;
    }
    return false;
}

/// True iff ANY method of the inner type contains
/// `@fieldParentPtr("<field_name>", ...)` — the canonical
/// embedded-view pattern where the inner navigates back to its
/// enclosing outer struct.  When any method (not just cleanup-named
/// ones) uses `@fieldParentPtr` with the field name, the inner is
/// an embedded view of the outer's storage.  Its cleanup is meant
/// to be invoked from outside the outer's deinit chain; the inner
/// gets freed when the outer is freed.
///
/// We intentionally check ALL methods, not just cleanup-named ones,
/// because the `@fieldParentPtr` call is often in a non-cleanup
/// accessor (`parent()`/`owner()`/`ctx()`) that the inner's `deinit`
/// then calls.  Following the call chain is out of scope; the
/// presence of any such accessor is sufficient signal.
fn innerDeinitUsesFieldParentPtr(
    tree: *const Ast,
    inner_ti: *const file_model.TypeInfo,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    for (inner_ti.methods) |m| {
        var t: Ast.TokenIndex = m.body_first;
        while (t + 3 <= m.body_last) : (t += 1) {
            if (tags[t] != .builtin) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), "@fieldParentPtr")) continue;
            if (tags[t + 1] != .l_paren) continue;
            if (tags[t + 2] != .string_literal) continue;
            // string_literal token includes the quotes — strip them.
            const lit = tree.tokenSlice(t + 2);
            if (lit.len < 2) continue;
            const inner = lit[1 .. lit.len - 1];
            if (std.mem.eql(u8, inner, field_name)) return true;
        }
    }
    return false;
}

/// True iff the type has an `init` / `create` / `from*` method
/// that takes a parameter of the same name as `field_name` —
/// evidence that the field is initialised from a caller-supplied
/// value (BORROWED in, not owned by this struct), so the outer's
/// deinit legitimately defers cleanup to the caller.
fn fieldIsCallerSupplied(
    tree: *const Ast,
    outer: *const file_model.TypeInfo,
    field_name: []const u8,
) bool {
    for (outer.methods) |m| {
        const is_constructor = std.mem.eql(u8, m.name, "init") or
            std.mem.eql(u8, m.name, "create") or
            std.mem.startsWith(u8, m.name, "from") or
            std.mem.eql(u8, m.name, "new");
        if (!is_constructor) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buf, m.fn_decl) orelse continue;
        var it = proto.iterate(tree);
        while (it.next()) |p| {
            const name_tok = p.name_token orelse continue;
            const name = tree.tokenSlice(name_tok);
            if (std.mem.eql(u8, name, field_name)) return true;
        }
    }
    return false;
}

/// True iff the field's declared type ends with `<suffix>`.  Looks
/// at the LAST identifier of the type chain (handles `Route.RefCount`
/// → "RefCount", `*lib.T.Inner` → "Inner") rather than the resolved
/// type's name which is the FIRST identifier.
fn fieldTypeTrailingNameEndsWith(tree: *const Ast, field: *const file_model.FieldInfo, suffix: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    var t = field.type_first;
    var last_id: ?[]const u8 = null;
    while (t <= field.type_last) : (t += 1) {
        if (tags[t] == .identifier) last_id = tree.tokenSlice(t);
    }
    const name = last_id orelse return false;
    return std.mem.endsWith(u8, name, suffix);
}


/// True iff the method's body contains an `if (X.<field>) |...cap...| { ... }`
/// shape where the if-body calls a cleanup-named method on `cap`.
/// Matches the canonical handling for `field: ?T` where T has a deinit:
///
///     pub fn deinit(self: *Outer, alloc: Allocator) void {
///         if (self.field) |*cap| cap.deinit(alloc);
///     }
///
/// Conservative: requires the if-condition's final tokens to be
/// `.<field>` (with our field name), and the capture token to be a
/// bare identifier (`|cap|` or `|*cap|`).  Doesn't try to match
/// `while (X.field) |cap|` (loops on an optional field are rare for
/// cleanup) or nested patterns.
fn bodyHandlesFieldViaUnwrap(tree: *const Ast, method: *const file_model.MethodInfo, field_name: []const u8, inner: *const file_model.TypeInfo) bool {
    const receiver = method.receiver orelse return false;
    const tags = tree.tokens.items(.tag);
    const first = method.body_first;
    const last = method.body_last;
    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] != .keyword_if) continue;
        if (tags[t + 1] != .l_paren) continue;
        const rparen = tokens.matchParen(tags, t + 1, last) orelse continue;
        // The optional must be this receiver's exact field, not another owner.
        if (rparen != t + 5 or tags[t + 2] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 2), receiver.name)) continue;
        if (tags[rparen - 2] != .period) continue;
        if (tags[rparen - 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(rparen - 1), field_name)) continue;
        // Capture: `|...|` immediately after `)`.
        if (rparen + 1 > last or tags[rparen + 1] != .pipe) continue;
        // Capture name: skip optional `*`.
        var cap_tok = rparen + 2;
        if (cap_tok <= last and tags[cap_tok] == .asterisk) cap_tok += 1;
        if (cap_tok > last or tags[cap_tok] != .identifier) continue;
        const cap_name = tree.tokenSlice(cap_tok);
        // Find the closing `|`, then the if-body extent.
        var close_pipe = cap_tok + 1;
        while (close_pipe <= last and tags[close_pipe] != .pipe) close_pipe += 1;
        if (close_pipe > last) continue;
        // Body extent: either `{ ... }` or a single statement up to `;`.
        const body_start = close_pipe + 1;
        if (body_start > last) continue;
        const body_end: Ast.TokenIndex = if (tags[body_start] == .l_brace)
            tokens.matchBrace(tags, body_start, last) orelse continue
        else
            tokens.findStmtSemicolon(tags, body_start, last) orelse continue;

        // Scan the body for `<cap_name>.<cleanup>(`.
        var k: Ast.TokenIndex = body_start;
        while (k + 3 <= body_end) : (k += 1) {
            if (tags[k] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(k), cap_name)) continue;
            if (tags[k + 1] != .period) continue;
            if (tags[k + 2] != .identifier) continue;
            if (tags[k + 3] != .l_paren) continue;
            const cleanup = inner.findMethod(tree.tokenSlice(k + 2)) orelse continue;
            if (cleanup.receiver != null and isCleanupName(cleanup.name)) return true;
        }
    }
    return false;
}

const isCleanupName = method_names.isCleanupMethodName;

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(problem.Problem),
    tree: *const Ast,
    field_tok: Ast.TokenIndex,
    field_name: []const u8,
    type_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "field `{s}: {s}` has a `deinit`-exposing type, but the outer struct's `deinit` doesn't call `<self>.{s}.deinit(...)` — the inner's owned non-memory resources (file handles, sockets, refs, mmaps) leak",
        .{ field_name, type_name, field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try problem.Pos.fromTokenStart(tree, field_tok),
        .end = try problem.Pos.fromTokenEnd(tree, field_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "outer deinit forgets inner field deinit fires" {
    try testing.expectFires(check, R,
        \\const MemoryAccessor = struct {
        \\    fd: i32 = -1,
        \\    pub fn deinit(self: *MemoryAccessor) void { self.fd = -1; }
        \\};
        \\const StackIterator = struct {
        \\    ma: MemoryAccessor,
        \\    pub fn deinit(it: *StackIterator) void {
        \\        _ = it;
        \\    }
        \\};
    );
}

test "outer deinit calls inner deinit — no fire" {
    try testing.expectNoFire(check,
        \\const MemoryAccessor = struct {
        \\    pub fn deinit(self: *MemoryAccessor) void { _ = self; }
        \\};
        \\const StackIterator = struct {
        \\    ma: MemoryAccessor,
        \\    pub fn deinit(it: *StackIterator) void {
        \\        it.ma.deinit();
        \\    }
        \\};
    );
}

test "field type has no deinit — no fire" {
    try testing.expectNoFire(check,
        \\const Plain = struct { x: u32 };
        \\const Outer = struct {
        \\    p: Plain,
        \\    pub fn deinit(self: *Outer) void { _ = self; }
        \\};
    );
}

test "pointer field (likely borrow) doesn't fire" {
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: ?*Inner,
        \\    pub fn deinit(self: *Outer) void {
        \\        _ = self;
        \\    }
        \\};
    );
}

test "optional value-typed field (?Inner) fires" {
    try testing.expectFires(check, R,
        \\const Inner = struct {
        \\    fd: i32 = -1,
        \\    pub fn deinit(self: *Inner) void { self.fd = -1; }
        \\};
        \\const Outer = struct {
        \\    inner: ?Inner,
        \\    pub fn deinit(self: *Outer) void {
        \\        _ = self;
        \\    }
        \\};
    );
}

test "optional field cleaned up via `if (x.f) |*cap| cap.deinit(...)` — no fire" {
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: ?Inner,
        \\    pub fn deinit(self: *Outer) void {
        \\        if (self.inner) |*cap| {
        \\            cap.deinit();
        \\        }
        \\    }
        \\};
    );
}

test "optional field unwrap with mismatched capture cleanup still recognized" {
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: ?Inner,
        \\    pub fn deinit(self: *Outer) void {
        \\        if (self.inner) |inner| inner.deinit();
        \\    }
        \\};
    );
}

test "embedded-view: @fieldParentPtr in non-cleanup helper suppresses — no fire" {
    // Mimics the js_valkey.zig pattern: SubscriptionCtx is embedded in
    // JSValkeyClient and navigates back via @fieldParentPtr in its `parent()`
    // helper method.  The outer's deinit legitimately doesn't call the inner's
    // deinit because the inner is a view that manages its own lifecycle.
    try testing.expectNoFire(check,
        \\const Client = struct {
        \\    ctx: Ctx,
        \\    pub fn deinit(this: *Client) void {
        \\        _ = this;
        \\    }
        \\};
        \\const Ctx = struct {
        \\    pub fn parent(this: *Ctx) *Client {
        \\        return @fieldParentPtr("ctx", this);
        \\    }
        \\    pub fn deinit(this: *Ctx) void {
        \\        _ = this.parent().someField;
        \\    }
        \\};
    );
}

test "skript regression: allocator free callback is not a composed destructor" {
    try testing.expectNoFire(check,
        \\const Callback = struct {
        \\    pub fn free(ctx: *anyopaque, bytes: []u8) void {
        \\        if (bytes.len != 0) _ = ctx;
        \\    }
        \\};
        \\const Outer = struct {
        \\    inner: Callback,
        \\    pub fn deinit(self: *Outer) void {
        \\        _ = self;
        \\    }
        \\};
    );
}

test "skript regression: receiver cleanup still requires outer deinit" {
    try testing.expectFires(check, R,
        \\const Resource = struct {
        \\    fd: i32 = -1,
        \\    pub fn free(self: *Resource) void {
        \\        self.fd = -1;
        \\    }
        \\};
        \\const Outer = struct {
        \\    inner: Resource,
        \\    pub fn deinit(self: *Outer) void {
        \\        _ = self;
        \\    }
        \\};
    );
}

// ocean#653: OwnedScene.deinit -> destroyScene(self) -> owned.scene.deinit.
// nogui#295,#296: Harness.deinit releases fake/threaded, not counter/stream.
test "composed owner follows exact free-function teardown argument" {
    try testing.expectNoFireTyped(check,
        \\const Scene = struct {
        \\    fd: i32,
        \\    fn deinit(self: *Scene) void { self.fd = -1; }
        \\};
        \\const Owned = struct {
        \\    scene: Scene,
        \\    fn deinit(self: *Owned) !void { return destroyScene(self); }
        \\};
        \\fn destroyScene(owned: *Owned) !void { owned.scene.deinit(); }
        \\pub fn run(owned: *Owned) !void { try owned.deinit(); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Scene = struct {
        \\    fd: i32,
        \\    fn deinit(self: *Scene) void { self.fd = -1; }
        \\};
        \\const Owned = struct {
        \\    scene: Scene,
        \\    fn deinit(self: *Owned, other: *Owned) void { destroyScene(other); _ = self; }
        \\};
        \\fn destroyScene(owned: *Owned) void { owned.scene.deinit(); }
        \\pub fn run(owned: *Owned, other: *Owned) void { owned.deinit(other); }
    );
}

test "composed owner does not treat field inspection or partial cleanup as destruction" {
    try testing.expectFiresTyped(check, R,
        \\const Scene = struct {
        \\    first: i32, second: i32,
        \\    fn deinit(self: *Scene) void { self.first = -1; self.second = -1; }
        \\};
        \\const Owned = struct {
        \\    scene: Scene,
        \\    fn deinit(self: *Owned) void { self.scene.first = -1; }
        \\};
        \\pub fn run(owned: *Owned) void { owned.deinit(); }
    );
}

test "composed owner preserves both outstanding PipeWire resources" {
    try testing.expectCount(check, R, 2,
        \\const Counter = struct {
        \\    live: usize,
        \\    fn release(self: *Counter) void { self.live -= 1; }
        \\};
        \\const Stream = struct {
        \\    live: usize,
        \\    fn stop(self: *Stream) void { self.live -= 1; }
        \\};
        \\const Harness = struct {
        \\    counter: Counter, stream: Stream, other: Counter,
        \\    fn deinit(self: *Harness) void { self.other.release(); self.* = undefined; }
        \\};
    );
}

test "composed owner optional cleanup must unwrap the same receiver" {
    try testing.expectFires(check, R,
        \\const Scene = struct {
        \\    fd: i32,
        \\    fn deinit(self: *Scene) void { self.fd = -1; }
        \\};
        \\const Owned = struct {
        \\    scene: ?Scene,
        \\    fn deinit(self: *Owned, other: *Owned) void {
        \\        _ = self;
        \\        if (other.scene) |*scene| scene.deinit();
        \\    }
        \\};
    );
}
