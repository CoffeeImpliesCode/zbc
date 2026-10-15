//! Reports a source-backed input/error-result contract mismatch, not panic
//! syntax alone. A direct callee must return a named capacity error for an
//! unchecked slice input, and its caller must explicitly declare that SAME
//! error as its result. The supported caller passes a local fixed byte array.
//!
//! This does not infer programmer intent. Infallible destructors, callbacks,
//! ownership invariants, required output, inferred error sets, unresolved calls,
//! and other control-flow shapes remain outside this proof. Their absence from
//! diagnostics is not a safety or recoverability certificate.
//!
//! Panic messages, function names, and test filenames carry no proof.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const AstIterator = @import("type_engine").AstIterator;
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "catch-error-panic";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .catch_error_panic)) return;
    // No untyped/name-based resolver fallback: source identity and actual
    // argument mapping are mandatory evidence.
    if (cache.zls == null) return;
    var remaining: usize = 50_000;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    var functions = tokens.iterFnDecls(tree);
    while (functions.next(&proto_buffer)) |function| {
        try charge(&remaining);
        const result_error = explicitResultError(tree, function.proto) orelse continue;
        if (!try isRootDeclaration(tree, function.node, &remaining)) continue;
        var parameters = function.proto.iterate(tree);
        const input = parameters.next() orelse continue;
        if (parameters.next() != null) continue;
        if (input.comptime_noalias != null) continue;
        const input_name = input.name_token orelse continue;
        if (!byteSlice(tree, input.type_expr orelse continue, true)) continue;

        // With exactly these two statements, no assertion, earlier call,
        // branch, defer, alias, or mutation can constrain the input length.
        const statements = twoStatements(tree, function.body) orelse continue;
        const buffer = tree.fullVarDecl(statements[0]) orelse continue;
        const buffer_name = buffer.ast.mut_token + 1;
        const buffer_type = buffer.ast.type_node.unwrap() orelse continue;
        if (!fixedByteArray(tree, buffer_type)) continue;
        const initializer = buffer.ast.init_node.unwrap() orelse continue;
        if (tree.firstToken(initializer) != tree.lastToken(initializer) or
            !std.mem.eql(u8, tree.tokenSlice(tree.firstToken(initializer)), "undefined")) continue;
        if (std.mem.eql(u8, tree.tokenSlice(buffer_name), tree.tokenSlice(input_name))) continue;

        const caught = statements[1];
        if (tree.nodeTag(caught) != .@"catch") continue;
        const catch_token = tree.nodeMainToken(caught);
        if (tree.tokenTag(catch_token + 1) != .pipe or
            tree.tokenTag(catch_token + 2) != .identifier or
            tree.tokenTag(catch_token + 3) != .pipe) continue;
        const call_node, const fallback = tree.nodeData(caught).node_and_node;
        if (!try panicCall(tree, fallback, input_name, buffer_name, &remaining)) continue;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, call_node) orelse continue;
        // A bare, non-generic direct call is the only transport modeled here.
        if (tree.nodeTag(call.ast.fn_expr) != .identifier or call.ast.params.len != 2) continue;
        const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)) orelse continue;
        if (actual.callee.tree != tree or actual.callee.call_node != call_node or
            actual.argument_offset != 0) continue;
        if (!try isRootDeclaration(tree, actual.callee.declaration, &remaining)) continue;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const output_argument = (try actual.callArgumentFor(cache, &argument_buffer, 0)) orelse continue;
        const input_argument = (try actual.callArgumentFor(cache, &argument_buffer, 1)) orelse continue;
        if (tree.nodeTag(output_argument) != .address_of or
            !identifierIs(tree, tree.nodeData(output_argument).node, tree.tokenSlice(buffer_name)) or
            !identifierIs(tree, input_argument, tree.tokenSlice(input_name))) continue;
        if (!try returnsInputCapacityError(tree, actual.callee.declaration, result_error, &remaining)) continue;
        try report(gpa, problems, tree, catch_token, tree.lastToken(fallback), result_error);
    }
}

fn charge(remaining: *usize) error{AnalysisBudgetExceeded}!void {
    if (remaining.* == 0) return error.AnalysisBudgetExceeded;
    remaining.* -= 1;
}

fn identifierIs(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    return tree.nodeTag(node) == .identifier and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
}

fn byteSlice(tree: *const Ast, node: Ast.Node.Index, is_const: bool) bool {
    const pointer = tree.fullPtrType(node) orelse return false;
    return pointer.size == .slice and
        (pointer.const_token != null) == is_const and
        pointer.allowzero_token == null and pointer.volatile_token == null and
        pointer.ast.sentinel.unwrap() == null and
        identifierIs(tree, pointer.ast.child_type, "u8");
}

fn fixedByteArray(tree: *const Ast, node: Ast.Node.Index) bool {
    if (tree.nodeTag(node) != .array_type) return false;
    const count, const element = tree.nodeData(node).node_and_node;
    if (!identifierIs(tree, element, "u8") or tree.nodeTag(count) != .number_literal) return false;
    const capacity = std.fmt.parseInt(usize, tree.tokenSlice(tree.nodeMainToken(count)), 0) catch return false;
    // There must be a representable longer input, not a maximal-sized array.
    return capacity < std.math.maxInt(usize) / 2;
}

fn twoStatements(tree: *const Ast, node: Ast.Node.Index) ?[2]Ast.Node.Index {
    switch (tree.nodeTag(node)) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => {},
        else => return null,
    }
    var children = AstIterator.init(tree, node);
    const first = children.next(tree) orelse return null;
    const second = children.next(tree) orelse return null;
    if (children.next(tree) != null) return null;
    return .{ first, second };
}

/// A literal singleton error set is an explicit result contract. Inferred
/// sets, anyerror, aliases, and unrelated errors do not establish this claim.
fn explicitResultError(tree: *const Ast, proto: Ast.full.FnProto) ?[]const u8 {
    const result = proto.ast.return_type.unwrap() orelse return null;
    if (tree.nodeTag(result) != .error_union) return null;
    const errors, const payload = tree.nodeData(result).node_and_node;
    if (!identifierIs(tree, payload, "void") or tree.nodeTag(errors) != .error_set_decl) return null;
    const left, const right = tree.nodeData(errors).token_and_token;
    if (right != left + 2 and right != left + 3) return null;
    if (tree.tokenTag(left + 1) != .identifier) return null;
    if (right == left + 3 and tree.tokenTag(left + 2) != .comma) return null;
    return tree.tokenSlice(left + 1);
}

fn panicCall(
    tree: *const Ast,
    node: Ast.Node.Index,
    input_name: Ast.TokenIndex,
    buffer_name: Ast.TokenIndex,
    remaining: *usize,
) !bool {
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    if (first + 1 > last) return false;
    if (tree.tokenTag(first) == .builtin and
        std.mem.eql(u8, tree.tokenSlice(first), "@panic") and
        tree.tokenTag(first + 1) == .l_paren) return true;
    if (first + 5 > last) return false;
    const tags = tree.tokens.items(.tag);
    if (!(tags[first] == .identifier and std.mem.eql(u8, tree.tokenSlice(first), "std") and
        tags[first + 1] == .period and tags[first + 2] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(first + 2), "debug") and
        tags[first + 3] == .period and tags[first + 4] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(first + 4), "panic") and tags[first + 5] == .l_paren)) return false;
    // The caller is a root declaration with only these two local bindings.
    // Tie the standard panic spelling to its import, not a same-named object.
    if (std.mem.eql(u8, tree.tokenSlice(input_name), "std") or
        std.mem.eql(u8, tree.tokenSlice(buffer_name), "std")) return false;
    for (tree.rootDecls()) |declaration| {
        try charge(remaining);
        const binding = tree.fullVarDecl(declaration) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(binding.ast.mut_token + 1), "std")) continue;
        if (tree.tokenTag(binding.ast.mut_token) != .keyword_const) return false;
        const initializer = binding.ast.init_node.unwrap() orelse return false;
        const imported = tokens.importLiteralFromTokens(tree, tree.firstToken(initializer), tree.lastToken(initializer)) orelse return false;
        return std.mem.eql(u8, imported, "std");
    }
    return false;
}

fn isRootDeclaration(tree: *const Ast, node: Ast.Node.Index, remaining: *usize) !bool {
    for (tree.rootDecls()) |declaration| {
        try charge(remaining);
        if (declaration == node) return true;
    }
    return false;
}

fn lengthOf(tree: *const Ast, node: Ast.Node.Index, parameter: Ast.TokenIndex) bool {
    if (tree.nodeTag(node) != .field_access) return false;
    const base, const field = tree.nodeData(node).node_and_token;
    return std.mem.eql(u8, tree.tokenSlice(field), "len") and
        identifierIs(tree, base, tree.tokenSlice(parameter));
}

fn returnsInputCapacityError(
    tree: *const Ast,
    declaration: Ast.Node.Index,
    result_error: []const u8,
    remaining: *usize,
) !bool {
    try charge(remaining);
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    const callee_error = explicitResultError(tree, proto) orelse return false;
    if (!std.mem.eql(u8, callee_error, result_error)) return false;
    var parameters = proto.iterate(tree);
    const output = parameters.next() orelse return false;
    const input = parameters.next() orelse return false;
    if (parameters.next() != null or output.comptime_noalias != null or input.comptime_noalias != null) return false;
    if (!byteSlice(tree, output.type_expr orelse return false, false) or
        !byteSlice(tree, input.type_expr orelse return false, true)) return false;
    const output_name = output.name_token orelse return false;
    const input_name = input.name_token orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var statements = AstIterator.init(tree, body);
    const first = statements.next(tree) orelse return false;
    const guard = tree.fullIf(first) orelse return false;
    if (guard.ast.else_expr.unwrap() != null or guard.payload_token != null) return false;
    if (tree.nodeTag(guard.ast.cond_expr) != .greater_than) return false;
    const input_length, const output_length = tree.nodeData(guard.ast.cond_expr).node_and_node;
    if (!lengthOf(tree, input_length, input_name) or !lengthOf(tree, output_length, output_name)) return false;
    const failure = guard.ast.then_expr;
    if (tree.nodeTag(failure) != .@"return") return false;
    const value = tree.nodeData(failure).opt_node.unwrap() orelse return false;
    return tree.nodeTag(value) == .error_value and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(value) + 2), result_error);
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    catch_tok: Ast.TokenIndex,
    end_tok: Ast.TokenIndex,
    result_error: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "unchecked input length reaches the callee's `error.{s}` capacity return, but this catch panics although the caller explicitly declares that same error result; propagate the declared input failure instead",
        .{result_error},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, catch_tok),
        .end = try Pos.fromTokenEnd(tree, end_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const copy_contract_source =
    \\const std = @import("std");
    \\fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
    \\    if (input.len > out.len) return error.BufferTooSmall;
    \\    @memcpy(out[0..input.len], input);
    \\}
    \\
;

test "catch-error-panic: @panic violates an explicit input-error result contract" {
    try testing.expectFiresTyped(check, R, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: std.debug.panic retains the explicit contract witness" {
    try testing.expectFiresTyped(check, R, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |err| std.debug.panic("copy failed: {}", .{err});
        \\}
    );
}

test "catch-error-panic: errorName is not a recoverability exemption" {
    try testing.expectFiresTyped(check, R, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |err| @panic(@errorName(err));
        \\}
    );
}

test "catch-error-panic: test helper and destructor names do not exempt a contract violation" {
    try testing.expectFiresTyped(check, R, copy_contract_source ++
        \\fn deinit(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("invariant in fixture");
        \\}
    );
}

test "catch-error-panic: catch unreachable is outside this rule" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch unreachable;
        \\}
    );
}

test "catch-error-panic: try preserves the declared error result" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    try copy(&buffer, input);
        \\}
    );
}

test "catch-error-panic: explicit return preserves the declared error result" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |err| return err;
        \\}
    );
}

test "catch-error-panic: an input guard prevents the unchecked-input witness" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    if (input.len > buffer.len) return error.BufferTooSmall;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: an infallible precondition wrapper has no propagation contract" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("precondition violated");
        \\}
    );
}

test "catch-error-panic: inferred errors do not declare the input failure recoverable" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) !void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: an unrelated declared error does not prove recoverability" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) error{Closed}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: unresolved source is unknown even with matching syntax" {
    try testing.expectNoFire(check,
        \\fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
        \\    if (input.len > out.len) return error.BufferTooSmall;
        \\    @memcpy(out[0..input.len], input);
        \\}
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: callee must actually return the input-dependent error" {
    try testing.expectNoFireTyped(check,
        \\fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
        \\    _ = out;
        \\    _ = input;
        \\}
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: callee error guard must use the mapped input and output" {
    try testing.expectNoFireTyped(check,
        \\fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
        \\    if (out.len > input.len) return error.BufferTooSmall;
        \\}
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}

// These fixtures retain the selected source shapes. No-fire means outside
// the proved input/result-contract boundary, not a release/output safety proof.
test "catch-error-panic: ocean 468 owned snapshot teardown is not a recoverable-input proof" {
    try testing.expectNoFireTyped(check,
        \\fn deinit(self: *@This()) void {
        \\    self.snapshot.release(self.io) catch |err| std.debug.panic("release: {s}", .{@errorName(err)});
        \\    self.snapshot.deinit();
        \\    self.policy.deinit();
        \\    self.store.deinit();
        \\    self.source.deinit();
        \\}
    );
}

test "catch-error-panic: ocean 532 allocator callback cannot propagate a journal failure" {
    try testing.expectNoFireTyped(check,
        \\fn allocate(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ra: usize) ?[*]u8 {
        \\    const self: *Shifting = @ptrCast(@alignCast(ctx));
        \\    _ = self.journal.append(tio, &.{}) catch |err| std.debug.panic("append: {s}", .{@errorName(err)});
        \\    return self.inner.rawAlloc(len, alignment, ra);
        \\}
    );
}

test "catch-error-panic: ocean 1646 pin unwinding has no input-error result contract" {
    try testing.expectNoFireTyped(check,
        \\fn releaseOrPanic(store: Core.ObjectStore, io: std.Io, handle: Core.Handle) void {
        \\    store.vtable.release(store.context, io, handle) catch |err| std.debug.panic("release: {s}", .{@errorName(err)});
        \\}
    );
}

test "catch-error-panic: ocean 1890 registry pin ownership remains unknown to this rule" {
    try testing.expectNoFireTyped(check,
        \\fn releasePin(table: *InvocationPins.Table, lease: LeaseId) void {
        \\    table.release(lease) catch |err| std.debug.panic("release: {s}", .{@errorName(err)});
        \\}
    );
}

test "catch-error-panic: ocean 1892 selected generation retirement is not an input proof" {
    try testing.expectNoFireTyped(check,
        \\fn retireInPlace(self: *Registry, published: *Generation) void {
        \\    if (!published.selected) return;
        \\    published.selected = false;
        \\    for (published.selection) |member| {
        \\        member.entry.table.retireFromSelection(member.pins) catch |err| std.debug.panic("retire: {s}", .{@errorName(err)});
        \\    }
        \\    _ = self;
        \\}
    );
}

test "catch-error-panic: ocean 2235 setup errdefer does not declare cleanup recoverable" {
    try testing.expectNoFireTyped(check,
        \\fn open(root: MappedTwoNetRoot) !*Self {
        \\    const storage = try root.timing_ctx.alloc(Self, 1);
        \\    const self = &storage[0];
        \\    self.* = .{ .root = root };
        \\    errdefer self.deinit() catch |err| std.debug.panic("cleanup: {s}", .{@errorName(err)});
        \\    try expectMappedLeaseBytes(root);
        \\    return self;
        \\}
    );
}

test "catch-error-panic: nogui 85 deferred read callback has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn deliver(_: *const Tagged, payload: *DeferredEffect, _: *Session) void {
        \\    payload.session.read(Tagged, payload.owner, payload.seen, readTagged) catch |err| std.debug.panic("read: {s}", .{@errorName(err)});
        \\    payload.queued.* = true;
        \\}
    );
}

test "catch-error-panic: nogui 92 fresh session errdefer remains outside the proof" {
    try testing.expectNoFireTyped(check,
        \\fn init(self: *Harness, gpa: std.mem.Allocator) !void {
        \\    var session = try Session.init(gpa);
        \\    errdefer session.deinit() catch |err| std.debug.panic("deinit: {s}", .{@errorName(err)});
        \\    self.owner = try session.create(Field, &initial);
        \\}
    );
}

test "catch-error-panic: nogui 93 harness destructor has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn deinit(self: *Harness) void {
        \\    self.clipboard.deinit();
        \\    self.session.deinit() catch |err| std.debug.panic("deinit: {s}", .{@errorName(err)});
        \\    self.* = undefined;
        \\}
    );
}

test "catch-error-panic: nogui 94 borrowed test output does not fabricate data" {
    try testing.expectNoFireTyped(check,
        \\fn readBorrowed(self: *Harness) []const u8 {
        \\    var borrowed: []const u8 = "";
        \\    self.session.read(Field, self.owner, &borrowed, readField) catch |err| std.debug.panic("read: {s}", .{@errorName(err)});
        \\    return borrowed;
        \\}
    );
}

test "catch-error-panic: nogui 95 snapshot assertion helper has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn snapshot(self: *Harness) Snapshot {
        \\    var state: Snapshot = .{};
        \\    self.session.read(Field, self.owner, &state, readSnapshot) catch |err| std.debug.panic("read: {s}", .{@errorName(err)});
        \\    return state;
        \\}
    );
}

test "catch-error-panic: nogui 96 fixture destructor has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn deinit(self: *Fixture) void {
        \\    self.publisher.deinit();
        \\    self.app.deinit();
        \\    self.session.deinit() catch |err| std.debug.panic("deinit: {s}", .{@errorName(err)});
        \\    self.* = undefined;
        \\}
    );
}

test "catch-error-panic: nogui 97 measurement teardown remains outside the proof" {
    try testing.expectNoFireTyped(check,
        \\fn taskCycle(gpa: std.mem.Allocator) !usize {
        \\    var session = try Session.init(gpa);
        \\    defer session.deinit() catch |err| std.debug.panic("deinit: {s}", .{@errorName(err)});
        \\    try session.shutdownTasks(0);
        \\    return 1;
        \\}
    );
}

test "catch-error-panic: nogui 98 measurement owner release remains outside the proof" {
    try testing.expectNoFireTyped(check,
        \\fn taskCycle(session: *Session) !usize {
        \\    var probe = try session.create(Probe, &probe_value);
        \\    defer session.release(Probe, &probe) catch |err| std.debug.panic("release: {s}", .{@errorName(err)});
        \\    try session.shutdownTasks(0);
        \\    return 1;
        \\}
    );
}

test "catch-error-panic: nogui 118 model destructor has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn deinit(self: *Ink) void {
        \\    self.dropLayout();
        \\    if (!self.released) {
        \\        self.session.release(Field, &self.owner) catch |err| std.debug.panic("release: {s}", .{@errorName(err)});
        \\        self.released = true;
        \\    }
        \\    self.* = undefined;
        \\}
    );
}

test "catch-error-panic: nogui 183 smoke ownership teardown remains outside the proof" {
    try testing.expectNoFireTyped(check,
        \\fn run(session: *Session, view: *View) !void {
        \\    defer {
        \\        if (view.field_model) |*model| {
        \\            session.release(FieldModel, model) catch |err| std.debug.panic("release: {s}", .{@errorName(err)});
        \\        }
        \\    }
        \\    try runHeadless();
        \\}
    );
}

test "catch-error-panic: nogui 184 required smoke evidence is not proved recoverable" {
    try testing.expectNoFireTyped(check,
        \\fn run(session: *Session, report: *Report) !void {
        \\    defer {
        \\        const result = session.deinit();
        \\        report.emit("shutdown: {s}", .{if (result) |_| "ok" else |err| @errorName(err)}) catch |err| std.debug.panic("write: {s}", .{@errorName(err)});
        \\    }
        \\    try runHeadless();
        \\}
    );
}

test "catch-error-panic: nogui 243 failed GPU drain precedes resource destruction" {
    try testing.expectNoFireTyped(check,
        \\fn deinit(self: *Self) void {
        \\    std.debug.assert(!self.recording);
        \\    self.gpu.waitIdle() catch |err| std.debug.panic("drain: {s}", .{@errorName(err)});
        \\    if (self.readback) |buffer| self.gpu.gpuFree(buffer);
        \\    self.renderer.deinit();
        \\}
    );
}

test "catch-error-panic: nogui 265 reserved ABI path has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn appendNodeReserved(self: *Adapter, node: semantics.Node) void {
        \\    self.appendNodeWith(true, node) catch |err| std.debug.panic("reserved: {s}", .{@errorName(err)});
        \\}
    );
}

test "catch-error-panic: nogui 389 accessibility fixture destructor has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn deinit(self: *Fixture) void {
        \\    self.adapter.deinit();
        \\    self.threaded.deinit();
        \\    self.publisher.deinit();
        \\    self.app.deinit();
        \\    self.session.deinit() catch |err| std.debug.panic("deinit: {s}", .{@errorName(err)});
        \\    self.* = undefined;
        \\}
    );
}

test "catch-error-panic: nogui 399 reentrant pump callback has no error result" {
    try testing.expectNoFireTyped(check,
        \\fn completed(self: *Nested, response: Response) void {
        \\    self.borrowed = response.action.key;
        \\    pushActivation(self.provider, "8|6|second");
        \\    self.inner_delivered = self.service.pump(0) catch |err| std.debug.panic("pump: {s}", .{@errorName(err)});
        \\    pushActivation(self.provider, "9|5|third");
        \\}
    );
}

test "catch-error-panic: renamed error and parameters keep the source contract" {
    try testing.expectFiresTyped(check, R,
        \\fn transfer(destination: []u8, data: []const u8) error{TooLong}!void {
        \\    if (data.len > destination.len) return error.TooLong;
        \\    @memcpy(destination[0..data.len], data);
        \\}
        \\fn fixture(bytes: []const u8) error{TooLong}!void {
        \\    var temporary: [16]u8 = undefined;
        \\    transfer(&temporary, bytes) catch |_| @panic("owned lease invariant");
        \\}
    );
}

test "catch-error-panic: a same-named nonpanic object does not prove a crash" {
    try testing.expectNoFireTyped(check,
        \\const std = struct {
        \\    const debug = struct {
        \\        fn panic(_: []const u8, _: anytype) void {}
        \\    };
        \\};
        \\fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
        \\    if (input.len > out.len) return error.BufferTooSmall;
        \\    @memcpy(out[0..input.len], input);
        \\}
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(&buffer, input) catch |err| std.debug.panic("copy failed", .{err});
        \\}
    );
}

test "catch-error-panic: swapped actual arguments do not borrow the input proof" {
    try testing.expectNoFireTyped(check, copy_contract_source ++
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    var buffer: [1024]u8 = undefined;
        \\    copy(@constCast(input), &buffer) catch |_| @panic("copy failed");
        \\}
    );
}

test "catch-error-panic: a callback alias does not borrow another callee's guard" {
    try testing.expectNoFireTyped(check,
        \\fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
        \\    if (input.len > out.len) return error.BufferTooSmall;
        \\    @memcpy(out[0..input.len], input);
        \\}
        \\const Other = struct {
        \\    fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
        \\        _ = out;
        \\        _ = input;
        \\    }
        \\};
        \\fn run(input: []const u8) error{BufferTooSmall}!void {
        \\    const operation = Other.copy;
        \\    var buffer: [1024]u8 = undefined;
        \\    operation(&buffer, input) catch |_| @panic("copy failed");
        \\}
    );
}
