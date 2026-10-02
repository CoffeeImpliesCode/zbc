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
const query = @import("../../ast/token_query.zig");
const tokens = @import("../../ast/tokens.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");

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

            // Direct: `<X>.<field>.<cleanup>(`.  X is wildcarded
            // (typically self/this).  The body pattern is built
            // per-field since `.text` needs the field's name.
            const cleanup_call = &[_]query.Atom{
                .{ .tok = .identifier },
                .{ .tok = .period },
                .{ .text = field.name },
                .{ .tok = .period },
                .{ .pred = isCleanupName },
                .paren_args,
            };
            if (mq.methodBodyContains(tree, deinit, cleanup_call)) continue;

            // Optional-unwrap: `if (X.field) |*?cap| { ... cap.<cleanup>(...); ... }`.
            // The user explicitly handled the optional and called
            // cleanup on the unwrapped capture — no leak.
            if (bodyHandlesFieldViaUnwrap(tree, deinit, field.name)) continue;

            // Helper-delegation: outer's deinit calls `<self>.<helper>()`
            // on the same type, and that helper's body cleans up the
            // field.  Common Bun shape:
            //     pub fn deinit(this: *Subprocess) void {
            //         this.finalizeSync();   ← helper does the cleanup
            //         alloc.destroy(this);
            //     }
            // One level of delegation only (no transitive chains).
            if (bodyHandlesFieldViaHelper(tree, model, deinit, outer, field.name, cleanup_call)) continue;

            // Partial sub-field cleanup: the deinit body mentions
            // `<self>.<field>.<subfield>...` somewhere.  Even without
            // a direct `<self>.<field>.deinit()`, partial cleanup
            // of inner resources is evidence the field is being
            // handled intentionally (rather than forgotten) — common
            // when the composed type's deinit signature requires
            // arguments the outer doesn't have, so the outer reaches
            // into specific owned sub-fields.
            if (methodBodyMentionsField(tree, deinit, field.name)) continue;

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

            // Externally-cleaned-up skip: when `<this>.<field>.<cleanup>(...)`
            // is invoked in OTHER methods of the same outer type
            // (multiple lifecycle stages — request setup, async
            // completion, ref drop), the field's cleanup is
            // routinely run before the outer's deinit ever fires.
            // The rule's prescription (call the inner's deinit from
            // the outer's deinit) would either double-deinit or
            // require the inner's deinit to be idempotent.  When the
            // inner's deinit IS idempotent (canonical bun shape:
            // \`this.* = .{}\` first, then frees), the call is safe
            // either way — but firing on this shape is noisy.
            if (siblingMethodsCleanField(tree, outer, deinit, field.name)) continue;

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

/// True iff the field's cleanup is invoked routinely at a different
/// lifecycle stage (request setup / async completion / ref drop /
/// etc.), so the outer's destructor doesn't need to re-do it.
/// The inner's deinit is conventionally idempotent in these shapes
/// (canonical bun: `this.* = .{}` first, then frees, so double-calls
/// are no-ops).
fn siblingMethodsCleanField(
    tree: *const Ast,
    outer: *const file_model.TypeInfo,
    deinit_method: *const file_model.MethodInfo,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    for (outer.methods) |*m| {
        if (m == deinit_method) continue;
        // Walk the body for `<X> . <field_name> . <cleanup-name> (`.
        var t: Ast.TokenIndex = m.body_first;
        while (t + 5 <= m.body_last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            // Word boundary at start.
            if (t > 0 and tags[t - 1] == .period) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field_name)) continue;
            if (tags[t + 3] != .period) continue;
            if (tags[t + 4] != .identifier) continue;
            if (tags[t + 5] != .l_paren) continue;
            const cleanup = tree.tokenSlice(t + 4);
            if (isCleanupName(cleanup)) return true;
        }
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

/// True iff `deinit`'s body calls `<self>.<helper>(...)` for a
/// helper method on the same outer type whose body mentions
/// `<self>.<field>` in any cleanup-shaped context.  Catches both:
///   1. helper does `<self>.<field>.<cleanup>(...)` directly
///   2. helper does `<self>.<field> = ...` reset followed by cleanup
///      elsewhere, or dispatches via tag-enum (`closeIO(.stdin)`).
/// One level of delegation only — chains of helpers aren't followed.
fn bodyHandlesFieldViaHelper(
    tree: *const Ast,
    model: *const file_model.FileModel,
    deinit: *const file_model.MethodInfo,
    outer: *const file_model.TypeInfo,
    field_name: []const u8,
    cleanup_call: []const query.Atom,
) bool {
    _ = model;
    const tags = tree.tokens.items(.tag);
    const first = deinit.body_first;
    const last = deinit.body_last;
    var t: Ast.TokenIndex = first;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        const helper_name = tree.tokenSlice(t + 2);
        if (std.mem.eql(u8, helper_name, "deinit")) continue;
        const helper = outer.findMethod(helper_name) orelse continue;
        // Tight check: helper does the canonical cleanup pattern.
        if (mq.methodBodyContains(tree, helper, cleanup_call)) return true;
        // Loose check: helper's body MENTIONS `<self>.<field>` at all
        // (covers tag-dispatch wrappers like `closeIO(.stdin)` whose
        // body inspects `<self>.stdin` and does the cleanup there).
        if (methodBodyMentionsField(tree, helper, field_name)) return true;
    }
    return false;
}

/// True iff the method's body contains either:
///   - `<id>.<field>` token-pair (object-field reference), OR
///   - `.<field>` tag-style reference (e.g. `closeIO(.stdin)` where
///     the field name matches a tag enum's variant).
/// Looser than a cleanup pattern match — used as a fall-through
/// signal that the helper at least references the field in some way.
fn methodBodyMentionsField(tree: *const Ast, method: *const file_model.MethodInfo, field_name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = method.body_first;
    while (t + 1 <= method.body_last) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t + 1), field_name)) return true;
    }
    return false;
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
fn bodyHandlesFieldViaUnwrap(tree: *const Ast, method: *const file_model.MethodInfo, field_name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    const first = method.body_first;
    const last = method.body_last;
    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] != .keyword_if) continue;
        if (tags[t + 1] != .l_paren) continue;
        const rparen = tokens.matchParen(tags, t + 1, last) orelse continue;
        // The condition's last two tokens must be `.<field_name>`.
        if (rparen < t + 4) continue;
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
            if (isCleanupName(tree.tokenSlice(k + 2))) return true;
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
        .start = problem.Pos.fromTokenStart(tree, field_tok),
        .end = problem.Pos.fromTokenEnd(tree, field_tok),
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
