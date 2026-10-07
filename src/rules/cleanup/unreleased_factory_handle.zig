//! GPU/refcounted-factory leak detector — `const <X> = [try]
//! <device>.<create-method>(...);` returns a refcounted handle
//! with initial refcount=1, but the local goes out of scope
//! without `defer <X>.release()` AND the handle isn't transferred
//! out of the fn (no `return <X>;` and no `<self>.<field> = <X>;`).
//!
//! Real-world: hexops/mach commits `ca08255e` and `3d4888f4` —
//! `device.createShaderModule()`, `getQueue()`, etc. each return
//! a fresh ref that the caller must release.  Examples that use
//! the handle transiently (as input to another create call) leak
//! one ref each invocation.
//!
//! Distinct from `unreleased-refs-on-error` which catches
//! `manager.reference()` increments on a loop without paired
//! release errdefer — that rule is about the addref side.  This
//! rule is about the INITIAL ref returned by a factory method on
//! the happy path.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;
const R = "unreleased-factory-handle";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .unreleased_factory_handle)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

const Handle = struct {
    name: []const u8,
    name_token: Ast.TokenIndex,
    method_tok: Ast.TokenIndex,
};

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const bindings = try cache.localBindings(proto, body);

    var handles: std.ArrayListUnmanaged(Handle) = .empty;
    defer handles.deinit(gpa);

    // Find `const|var X = [try] <recv>.<factoryMethod>(...)` bindings.
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        const c = b.asCall() orelse continue;
        const method = c.method orelse continue;
        if (!isFactoryMethodName(method)) continue;
        try handles.append(gpa, .{
            .name = b.name,
            .name_token = b.name_token,
            .method_tok = c.method_token.?,
        });
    }
    if (handles.items.len == 0) return;

    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    for (handles.items) |h| {
        if (hasDeferRelease(tree, first, last, h.name)) continue;
        if (handleEscapes(tree, first, last, h.name)) continue;
        try report(gpa, problems, tree, h);
    }
}

fn isFactoryMethodName(name: []const u8) bool {
    // Only `create*` factory methods that reliably return a fresh
    // refcounted handle.  `getQueue` / `acquireCurrentTexture` /
    // similar are deliberately omitted — depending on the
    // implementation they may return a BORROWED pointer to the
    // device's own field rather than a freshly-counted handle,
    // and flagging them produces FPs.
    return std.mem.eql(u8, name, "createShaderModule") or
        std.mem.eql(u8, name, "createPipelineLayout") or
        std.mem.eql(u8, name, "createBindGroup") or
        std.mem.eql(u8, name, "createBindGroupLayout") or
        std.mem.eql(u8, name, "createComputePipeline") or
        std.mem.eql(u8, name, "createRenderPipeline") or
        std.mem.eql(u8, name, "createBuffer") or
        std.mem.eql(u8, name, "createTexture") or
        std.mem.eql(u8, name, "createSampler") or
        std.mem.eql(u8, name, "createCommandEncoder") or
        std.mem.eql(u8, name, "createComputePassEncoder") or
        std.mem.eql(u8, name, "createRenderPassEncoder") or
        std.mem.eql(u8, name, "createRenderBundleEncoder") or
        std.mem.eql(u8, name, "createQuerySet") or
        std.mem.eql(u8, name, "createTextureView");
}

fn isReleaseMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "deref") or
        std.mem.eql(u8, name, "unref");
}

/// True iff `[start, last]` contains `defer <name>.<release>()` or
/// `errdefer <name>.<release>()`.  Block-form `defer { <name>...`
/// is also accepted (one leading `{` between the keyword and the
/// receiver).
fn hasDeferRelease(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] != .keyword_defer and tags[t] != .keyword_errdefer) continue;
        var u: Ast.TokenIndex = t + 1;
        // Optional `|err|` capture on errdefer.
        if (u <= last and tags[u] == .pipe) {
            u += 1;
            while (u <= last and tags[u] != .pipe) : (u += 1) {}
            if (u > last) return false;
            u += 1;
        }
        // Optional `{` (block form).
        if (u <= last and tags[u] == .l_brace) u += 1;
        if (u + 3 > last) continue;
        const release_call = [_]Atom{
            .{ .text = name },
            .{ .tok = .period },
            .{ .pred = isReleaseMethodName },
            .{ .tok = .l_paren },
        };
        if (query.matchAt(tree, &release_call, u, last, null) != null) return true;
    }
    return false;
}

/// True iff the handle escapes via:
///   - `return <expr ...name...>` — return statement
///   - `<X> = <expr ...name...>` — assignment RHS (struct-field
///     or `.field = name` in a struct literal)
///   - positional arg to a fn call (`foo(name)` / `foo(a, name, b)`).
///
/// Skips the binding site itself.  Skips `_ = name;` discards.
fn handleEscapes(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        // Skip the binding site itself (`const|var <name> = ...`).
        if (t >= 1 and (tags[t - 1] == .keyword_const or tags[t - 1] == .keyword_var)) continue;
        // Preceded by `=` → assignment RHS = escape.  EXCEPT `_ = name`.
        if (t >= 1 and tags[t - 1] == .equal) {
            const lhs_is_underscore = t >= 2 and
                tags[t - 2] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t - 2), "_");
            if (!lhs_is_underscore) return true;
            continue;
        }
        // Preceded by `return` → escape.
        if (t >= 1 and tags[t - 1] == .keyword_return) return true;
        // `, name [,)]` — positional arg continuation.
        if (t >= 1 and tags[t - 1] == .comma and
            t + 1 <= last and (tags[t + 1] == .comma or tags[t + 1] == .r_paren or tags[t + 1] == .r_brace))
            return true;
        // `( name [,)]` — positional first arg.
        if (t >= 1 and tags[t - 1] == .l_paren and
            t + 1 <= last and (tags[t + 1] == .comma or tags[t + 1] == .r_paren))
            return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    h: Handle,
) !void {
    const method = tree.tokenSlice(h.method_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` was acquired from `.{s}()` (returns a refcounted handle with initial refcount=1), but no `defer {s}.release()` is registered and the handle isn't returned or stored — one ref leaks every call",
        .{ h.name, method, h.name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, h.name_token),
        .end = try Pos.fromTokenEnd(tree, h.name_token),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "createPipelineLayout without defer release fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Device = struct {
        \\    pub fn createPipelineLayout(_: *Device, _: anytype) *u8 { return undefined; }
        \\};
        \\pub fn build(device: *Device, desc: anytype) void {
        \\    const layout = device.createPipelineLayout(desc);
        \\    _ = layout;
        \\}
    );
}

test "with defer release doesn't fire" {
    try testing.expectNoFire(check,
        \\const Layout = struct { pub fn release(_: *Layout) void {} };
        \\const Device = struct {
        \\    pub fn createPipelineLayout(_: *Device, _: anytype) *Layout { return undefined; }
        \\};
        \\pub fn build(device: *Device, desc: anytype) void {
        \\    const layout = device.createPipelineLayout(desc);
        \\    defer layout.release();
        \\    _ = layout;
        \\}
    );
}

test "returned handle doesn't fire (ownership transfer)" {
    try testing.expectNoFire(check,
        \\const Layout = struct {};
        \\const Device = struct {
        \\    pub fn createPipelineLayout(_: *Device, _: anytype) *Layout { return undefined; }
        \\};
        \\pub fn build(device: *Device, desc: anytype) *Layout {
        \\    const layout = device.createPipelineLayout(desc);
        \\    return layout;
        \\}
    );
}

test "stored in struct field doesn't fire" {
    try testing.expectNoFire(check,
        \\const Layout = struct {};
        \\const Device = struct {
        \\    pub fn createPipelineLayout(_: *Device, _: anytype) *Layout { return undefined; }
        \\};
        \\const Renderer = struct {
        \\    layout: *Layout,
        \\    pub fn setup(self: *Renderer, device: *Device, desc: anytype) void {
        \\        const layout = device.createPipelineLayout(desc);
        \\        self.layout = layout;
        \\    }
        \\};
    );
}

test "non-factory method (getStatus) skipped" {
    try testing.expectNoFire(check,
        \\const Device = struct {
        \\    pub fn getStatus(_: *Device) u8 { return 0; }
        \\};
        \\pub fn check(device: *Device) void {
        \\    const status = device.getStatus();
        \\    _ = status;
        \\}
    );
}
