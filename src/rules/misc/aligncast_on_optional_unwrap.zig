//! Detects `@alignCast(x.?)` — combining a forced optional unwrap with an
//! alignment assertion inside the same `@alignCast` call.  If `x` is null the
//! forced `.?` panics; if non-null the subsequent alignment check may also
//! panic on unaligned input.  The correct form is to use a non-optional type
//! for the pointer, or to guard with `orelse` before casting.
//!
//! Real-world instance:
//!   - tigerbeetle/tigerbeetle#3717 (io: even_listen):
//!     `@ptrCast(@alignCast(ctx.?))` — the nullable context was forced-unwrapped
//!     inside the align-cast; both the null-deref and the misalign checks were
//!     implicit.  Fix: changed all `?*anyopaque` context parameters to
//!     `*anyopaque`, eliminating the `.?` at every dereference site.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `builtin("@alignCast") l_paren identifier period question_mark r_paren`
//!   — 6 tokens.  Fire at the `@alignCast` builtin token.
//!
//! A closed registration can also discharge both hazards: the callback must
//! receive the unchanged context field from its registered aggregate, and
//! every registration must supply an ordinary address of the recovered type.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const pointer_proofs = @import("aligncast_on_byte_slice.zig");
const callback_provenance = @import("../../model/callback_provenance.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "aligncast-on-optional-unwrap";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .aligncast_on_optional_unwrap)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    if (first + 5 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Pattern: @alignCast ( identifier . ? )
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@alignCast")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .question_mark) continue;
        if (tags[t + 5] != .r_paren) continue;

        if (pointer_proofs.nullRejectedBefore(tree, t, tree.tokenSlice(t + 2)) and
            try typedParameterMatchesTarget(cache, proto, t, tree.tokenSlice(t + 2))) continue;
        if (try callback_provenance.callbackParameterProven(cache, proto, t)) continue;

        try report(gpa, problems, tree, t);
    }
}

/// A null guard does not validate an opaque or explicitly underaligned
/// address. Only the same ordinary typed pointee is known aligned here.
fn typedParameterMatchesTarget(
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    cast: Ast.TokenIndex,
    name: []const u8,
) !bool {
    const resolver = cache.zls orelse return false;
    const tree = cache.tree;
    const frame = resolver.resolutionFrame();
    var source_node: ?Ast.Node.Index = null;
    var parameters = proto.iterate(tree);
    while (parameters.next()) |parameter| {
        const token = parameter.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(token), name))
            source_node = parameter.type_expr orelse return false;
    }
    const source_type_node = source_node orelse return false;
    const optional = (try frame.typeOfNode(source_type_node)) orelse return false;
    if (resolver.typeTag(optional) != .optional) return false;
    const source = (try resolver.normalizedType(
        resolver.childType(optional) orelse return false,
    )) orelse return false;
    if (resolver.pointerAllowsZero(source) != false) return false;
    const source_syntax = (try callback_provenance.pointerTypeSource(
        frame, source_type_node, 0,
    )) orelse return false;
    const source_pointer = source_syntax.frame.handle.document.tree.fullPtrType(source_syntax.node).?;
    if (source_pointer.ast.align_node.unwrap() != null or
        source_pointer.allowzero_token != null) return false;

    var target_node: ?Ast.Node.Index = null;
    for (1..tree.nodes.len) |raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.fullVarDecl(node)) |local| {
            const init = local.ast.init_node.unwrap() orelse continue;
            if (!isRecoveryExpression(tree, init, cast)) continue;
            target_node = local.ast.type_node.unwrap() orelse return false;
            break;
        }
        if (tree.nodeTag(node) == .@"return") {
            const expression = tree.nodeData(node).opt_node.unwrap() orelse continue;
            if (!isRecoveryExpression(tree, expression, cast)) continue;
            target_node = proto.ast.return_type.unwrap() orelse return false;
            if (tree.nodeTag(target_node.?) == .error_union)
                target_node = tree.nodeData(target_node.?).node_and_node[1];
            break;
        }
    }
    const target_type_node = target_node orelse return false;
    const target = (try frame.typeOfNode(target_type_node)) orelse return false;
    if (resolver.pointerSize(source) != resolver.pointerSize(target)) return false;
    const size = resolver.pointerSize(target) orelse return false;
    if (size != .one and size != .many) return false;
    const target_syntax = (try callback_provenance.pointerTypeSource(
        frame, target_type_node, 0,
    )) orelse return false;
    const target_pointer = target_syntax.frame.handle.document.tree.fullPtrType(target_syntax.node).?;
    if (target_pointer.ast.align_node.unwrap() != null or
        target_pointer.allowzero_token != null) return false;
    const source_child = (try resolver.normalizedType(
        resolver.childType(source) orelse return false,
    )) orelse return false;
    const target_child = (try resolver.normalizedType(
        resolver.childType(target) orelse return false,
    )) orelse return false;
    return @import("type_engine").TypeResolver.ActualType.eql(source_child, target_child);
}

fn isRecoveryExpression(tree: *const Ast, node: Ast.Node.Index, cast: Ast.TokenIndex) bool {
    if (tree.nodeMainToken(node) == cast) return true;
    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@ptrCast")) return false;
    var buffer: [2]Ast.Node.Index = undefined;
    const arguments = tree.builtinCallParams(&buffer, node) orelse return false;
    return arguments.len == 1 and tree.nodeMainToken(arguments[0]) == cast;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    aligncast_tok: Ast.TokenIndex,
) !void {
    const name = tree.tokenSlice(aligncast_tok + 2);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@alignCast({s}.?)` — the forced `.?` panics when `{s}` is null and the alignment assertion may also panic on unaligned data; use a non-optional type for the pointer, or guard with `orelse` before casting",
        .{ name, name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, aligncast_tok),
        .end = try Pos.fromTokenEnd(tree, aligncast_tok + 5),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "aligncast-on-optional-unwrap: opaque callback signature alone does not prove a nonnull argument" {
    try testing.expectFires(check, R,
        \\fn dispatchCallback(ctx: ?*anyopaque) void {
        \\    const self: *Handler = @ptrCast(@alignCast(ctx.?));
        \\    self.handle();
        \\}
        \\
    );
}

test "aligncast-on-optional-unwrap: const opaque signature alone does not prove a nonnull argument" {
    try testing.expectFires(check, R,
        \\fn dispatchCallback(data: ?*const anyopaque) void {
        \\    const self: *const Handler = @ptrCast(@alignCast(data.?));
        \\    self.handle();
        \\}
        \\
    );
}

test "aligncast-on-optional-unwrap: genuinely-nullable typed optional param still fires" {
    try testing.expectFires(check, R,
        \\fn use(p: ?*Foo) void {
        \\    const f: *Foo = @alignCast(p.?);
        \\    f.run();
        \\}
        \\
    );
}

test "aligncast-on-optional-unwrap: non-optional does not fire" {
    try testing.expectNoFire(check,
        \\fn dispatchCallback(ctx: *anyopaque) void {
        \\    const self: *Handler = @ptrCast(@alignCast(ctx));
        \\    self.handle();
        \\}
        \\
    );
}

test "aligncast-on-optional-unwrap: orelse guard does not fire" {
    try testing.expectNoFire(check,
        \\fn dispatchCallback(ctx: ?*anyopaque) void {
        \\    const self: *Handler = @ptrCast(@alignCast(ctx orelse return));
        \\    self.handle();
        \\}
        \\
    );
}

test "aligncast-on-optional-unwrap: standalone .? not in alignCast does not fire" {
    try testing.expectNoFire(check,
        \\fn getHandler(opt: ?*Handler) *Handler {
        \\    return opt.?;
        \\}
        \\
    );
}

test "optional pointer: a dominating null rejection proves the unwrap" {
    try testing.expectNoFireTyped(check,
        \\const Foo = struct { value: u32 };
        \\fn recover(p: ?*Foo) !*Foo {
        \\    if (p == null) return error.Missing;
        \\    return @alignCast(p.?);
        \\}
    );
}

test "optional pointer: branch-only null rejection does not prove the unwrap" {
    try testing.expectFires(check, R,
        \\fn recover(p: ?*Foo, validate: bool) !*Foo {
        \\    if (validate) {
        \\        if (p == null) return error.Missing;
        \\    }
        \\    return @alignCast(p.?);
        \\}
    );
}

test "optional pointer: replacing the guarded value invalidates the proof" {
    try testing.expectFires(check, R,
        \\fn recover(input: ?*Foo, replacement: ?*Foo) !*Foo {
        \\    var p = input;
        \\    if (p == null) return error.Missing;
        \\    p = replacement;
        \\    return @alignCast(p.?);
        \\}
    );
}

test "optional pointer: null rejection does not establish opaque or underaligned provenance" {
    try testing.expectFires(check, R,
        \\fn recover(p: ?*anyopaque) !*Foo {
        \\    if (p == null) return error.Missing;
        \\    const typed: *Foo = @ptrCast(@alignCast(p.?));
        \\    return typed;
        \\}
    );
    try testing.expectFires(check, R,
        \\fn recover(p: ?*align(1) Foo) !*Foo {
        \\    if (p == null) return error.Missing;
        \\    return @alignCast(p.?);
        \\}
    );
}

test "optional callback: closed payload registrations retain native typed addresses" {
    try testing.expectNoFireTyped(check,
        \\const NativePayload = struct { bytes: []const u8 };
        \\const PayloadSource = struct {
        \\    context: ?*anyopaque,
        \\    byte_length: usize,
        \\    read: *const fn (?*anyopaque, usize, []u8) usize,
        \\};
        \\fn readNativePayload(context: ?*anyopaque, _: usize, out: []u8) usize {
        \\    const payload: *NativePayload = @ptrCast(@alignCast(context.?));
        \\    out[0] = payload.bytes[0];
        \\    return 1;
        \\}
        \\fn publish(payload: PayloadSource) usize {
        \\    var out: [1]u8 = undefined;
        \\    return payload.read(payload.context, 0, &out);
        \\}
        \\pub fn run() usize {
        \\    var selected_payload: NativePayload = .{ .bytes = "a" };
        \\    const payload: PayloadSource = .{
        \\        .context = &selected_payload, .byte_length = 1, .read = readNativePayload,
        \\    };
        \\    return publish(payload);
        \\}
    );
}

test "optional callback: repeated inline retained payload registrations stay paired" {
    try testing.expectNoFireTyped(check,
        \\const RetainedPayload = struct { bytes: []const u8 };
        \\const PayloadSource = struct {
        \\    context: ?*anyopaque, read: *const fn (?*anyopaque) usize,
        \\};
        \\fn readRetainedPayload(context: ?*anyopaque) usize {
        \\    const payload: *const RetainedPayload = @ptrCast(@alignCast(context.?));
        \\    return payload.bytes.len;
        \\}
        \\fn publish(payload: PayloadSource) usize { return payload.read(payload.context); }
        \\pub fn first() usize {
        \\    var payload_context: RetainedPayload = .{ .bytes = "a" };
        \\    return publish(.{ .context = &payload_context, .read = readRetainedPayload });
        \\}
        \\pub fn second() usize {
        \\    var payload_context: RetainedPayload = .{ .bytes = "bc" };
        \\    return publish(.{ .context = &payload_context, .read = readRetainedPayload });
        \\}
    );
}

test "optional callback: null executor does not contaminate a second-parameter work context" {
    try testing.expectNoFireTyped(check,
        \\const Harness = struct {
        \\    const State = struct { count: usize = 0 };
        \\    fn work(_: usize, context: ?*anyopaque) void {
        \\        const state: *State = @ptrCast(@alignCast(context.?));
        \\        state.count += 1;
        \\    }
        \\    fn runReverse(_: usize, _: ?*anyopaque) void {}
        \\};
        \\const Worker = struct {
        \\    context: ?*anyopaque, run_fn: *const fn (usize, ?*anyopaque) void,
        \\};
        \\fn execute(executor: Worker, worker: Worker) void {
        \\    executor.run_fn(0, executor.context);
        \\    worker.run_fn(0, worker.context);
        \\}
        \\pub fn run() void {
        \\    var state: Harness.State = .{};
        \\    execute(.{ .context = null, .run_fn = Harness.runReverse },
        \\        .{ .context = &state, .run_fn = Harness.work });
        \\}
    );
}

test "optional callback: unknown dispatcher cannot certify a registered context" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct { count: usize = 0 };
        \\const Worker = struct {
        \\    context: ?*anyopaque, run_fn: *const fn (?*anyopaque) void,
        \\};
        \\fn work(context: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(context.?));
        \\    state.count += 1;
        \\}
        \\extern fn execute(worker: Worker) void;
        \\pub fn run() void {
        \\    var state: State = .{};
        \\    execute(.{ .context = &state, .run_fn = work });
        \\}
    );
}

const returned_fixture =
    \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
    \\const State = struct {
    \\    calls: usize = 0,
    \\    fn onEvent(raw: ?*anyopaque) void {
    \\        const self: *State = @ptrCast(@alignCast(raw.?));
    \\        self.calls += 1;
    \\    }
    \\    fn reader(self: *State) Callback { return .{ .context = self, .invoke = onEvent }; }
    \\};
    \\fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
;

test "optional callback: returned method aggregate preserves nonnull self" {
    try testing.expectNoFireTyped(check, returned_fixture ++
        \\pub fn safePath() void {
        \\    var state: State = .{};
        \\    const callback = state.reader();
        \\    dispatch(callback);
        \\    dispatch(state.reader());
        \\}
    );
}

test "optional callback: returned method aggregate retains null context finding" {
    try testing.expectFiresTyped(check, R,
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
        \\const State = struct {
        \\    calls: usize = 0,
        \\    fn onEvent(raw: ?*anyopaque) void {
        \\        const self: *State = @ptrCast(@alignCast(raw.?));
        \\        self.calls += 1;
        \\    }
        \\    fn reader(self: *State) Callback {
        \\        _ = self;
        \\        return .{ .context = null, .invoke = onEvent };
        \\    }
        \\};
        \\fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
        \\pub fn unsafePath() void { var state: State = .{}; dispatch(state.reader()); }
    );
}

test "optional callback: returned aggregate escape keeps the finding" {
    try testing.expectFiresTyped(check, R, returned_fixture ++
        \\extern fn unknown(callback: Callback) void;
        \\pub fn unsafePath() void {
        \\    var state: State = .{};
        \\    const callback = state.reader();
        \\    dispatch(callback);
        \\    unknown(callback);
        \\}
    );
}

const slice_fixture =
    \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) u8 };
    \\fn onBytes(raw: ?*anyopaque) u8 {
    \\    const bytes: [*]const u8 = @ptrCast(@alignCast(raw.?));
    \\    return bytes[0];
    \\}
    \\fn dispatch(callback: Callback) u8 { return callback.invoke(callback.context); }
;

test "optional callback: const cast slice pointer proves byte alignment" {
    try testing.expectNoFireTyped(check, slice_fixture ++
        \\pub fn safePath(bytes: []const u8) u8 {
        \\    return dispatch(.{ .context = @constCast(bytes.ptr), .invoke = onBytes });
        \\}
    );
}

test "optional callback: slice registration null control keeps the finding" {
    try testing.expectFiresTyped(check, R, slice_fixture ++
        \\pub fn unsafePath(bytes: []const u8) u8 {
        \\    _ = dispatch(.{ .context = @constCast(bytes.ptr), .invoke = onBytes });
        \\    return dispatch(.{ .context = null, .invoke = onBytes });
        \\}
    );
}

test "optional callback: byte slice cannot prove stronger destination alignment" {
    try testing.expectFiresTyped(check, R,
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) u32 };
        \\fn onBytes(raw: ?*anyopaque) u32 {
        \\    const words: [*]const u32 = @ptrCast(@alignCast(raw.?));
        \\    return words[0];
        \\}
        \\fn dispatch(callback: Callback) u32 { return callback.invoke(callback.context); }
        \\pub fn unsafePath(bytes: []const u8) u32 {
        \\    return dispatch(.{ .context = @constCast(bytes.ptr), .invoke = onBytes });
        \\}
    );
}

fn expectImportedCallback(source: [:0]const u8, expected: usize) !void {
    const engine = @import("type_engine");
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "api.zig",
        .data =
        \\pub const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
        \\pub fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
        \\pub fn direct(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
    });
    const directory = try tmp.dir.realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const cache = try gpa.create(file_cache_mod.FileCache);
    defer gpa.destroy(cache);
    cache.* = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(expected, problems.items.len);
    for (problems.items) |finding| try std.testing.expectEqualStrings(R, finding.rule_id);
}

const state_fixture =
    \\const State = struct {
    \\    calls: usize = 0,
    \\    fn onEvent(raw: ?*anyopaque) void {
    \\        const self: *State = @ptrCast(@alignCast(raw.?));
    \\        self.calls += 1;
    \\    }
    \\};
;

const imported_fixture = "const api = @import(\"api.zig\");\n" ++ state_fixture;

const pointer_fixture = state_fixture ++
    \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
    \\fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
;

test "optional callback: cross file dispatcher preserves the registration pair" {
    try expectImportedCallback(imported_fixture ++
        \\pub fn safePath() void {
        \\    var state: State = .{};
        \\    api.dispatch(.{ .context = &state, .invoke = State.onEvent });
        \\}
    , 0);
}
test "optional callback: imported direct dispatcher preserves the registration pair" {
    try expectImportedCallback(imported_fixture ++
        \\pub fn safePath() void {
        \\    var state: State = .{};
        \\    api.direct(&state, State.onEvent);
        \\}
    , 0);
}

test "optional callback: cross file dispatcher null control keeps the finding" {
    try expectImportedCallback(imported_fixture ++
        \\pub fn unsafePath() void {
        \\    api.dispatch(.{ .context = null, .invoke = State.onEvent });
        \\}
    , 1);
}

test "optional callback: cross file dispatcher requires every registration" {
    try expectImportedCallback(imported_fixture ++
        \\pub fn unsafePath(context: ?*anyopaque) void {
        \\    var state: State = .{};
        \\    api.dispatch(.{ .context = &state, .invoke = State.onEvent });
        \\    api.dispatch(.{ .context = context, .invoke = State.onEvent });
        \\}
    , 1);
}

test "optional callback: typed pointer parameter preserves nonnull alignment" {
    try testing.expectNoFireTyped(check, pointer_fixture ++
        \\pub fn safePath(state: *State) void {
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: allocated pointer retains its declared alignment" {
    try testing.expectNoFireTyped(check, pointer_fixture ++
        \\const std = @import("std");
        \\pub fn safePath(allocator: std.mem.Allocator) !void {
        \\    const state = try allocator.create(State);
        \\    defer allocator.destroy(state);
        \\    state.* = .{};
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: underaligned pointer parameter keeps the finding" {
    try testing.expectFiresTyped(check, R, pointer_fixture ++
        \\pub fn unsafePath(state: *align(1) State) void {
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: allowzero pointer parameter keeps the finding" {
    try testing.expectFiresTyped(check, R, pointer_fixture ++
        \\pub fn unsafePath(state: *allowzero State) void {
        \\    dispatch(.{ .context = @ptrCast(state), .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: allowzero slice pointer keeps the finding" {
    try testing.expectFiresTyped(check, R, slice_fixture ++
        \\pub fn unsafePath(bytes: []allowzero const u8) u8 {
        \\    return dispatch(.{ .context = @ptrCast(@constCast(bytes.ptr)), .invoke = onBytes });
        \\}
    );
}

test "optional callback: ordinary slice element alignment survives const cast" {
    try testing.expectNoFireTyped(check,
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) u32 };
        \\fn onWords(raw: ?*anyopaque) u32 {
        \\    const words: [*]const u32 = @ptrCast(@alignCast(raw.?));
        \\    return words[0];
        \\}
        \\fn dispatch(callback: Callback) u32 { return callback.invoke(callback.context); }
        \\pub fn safePath(words: []const u32) u32 {
        \\    return dispatch(.{ .context = @constCast(words.ptr), .invoke = onWords });
        \\}
    );
}

test "optional callback: underaligned slice element pointer keeps the finding" {
    try testing.expectFiresTyped(check, R,
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) u32 };
        \\fn onWords(raw: ?*anyopaque) u32 {
        \\    const words: [*]const u32 = @ptrCast(@alignCast(raw.?));
        \\    return words[0];
        \\}
        \\fn dispatch(callback: Callback) u32 { return callback.invoke(callback.context); }
        \\pub fn unsafePath(words: []align(1) const u32) u32 {
        \\    return dispatch(.{ .context = @constCast(words.ptr), .invoke = onWords });
        \\}
    );
}
test "optional callback: generic typed registration keeps callable paired with its receiver" {
    try testing.expectNoFireTyped(check,
        \\const Receiver = struct {
        \\    calls: usize = 0,
        \\    fn onEvent(context: ?*anyopaque) void {
        \\        const self: *Receiver = @ptrCast(@alignCast(context.?));
        \\        self.calls += 1;
        \\    }
        \\};
        \\fn dispatch(comptime T: type, context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    _ = T;
        \\    callback(context);
        \\}
        \\fn register(comptime T: type, receiver: *T) void {
        \\    dispatch(T, receiver, T.onEvent);
        \\}
        \\pub fn safePath() void {
        \\    var receiver: Receiver = .{};
        \\    register(Receiver, &receiver);
        \\}
    );
}

test "optional callback: direct synchronous callback and typed local stay paired" {
    try testing.expectNoFireTyped(check,
        \\const Visit = struct {
        \\    ordinals: [1]usize = undefined,
        \\    len: usize = 0,
        \\    fn visit(context: ?*anyopaque, ordinal: usize) void {
        \\        const self: *@This() = @ptrCast(@alignCast(context.?));
        \\        self.ordinals[self.len] = ordinal;
        \\        self.len += 1;
        \\    }
        \\};
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque, usize) void, ordinal: usize) void {
        \\    callback(context, ordinal);
        \\}
        \\pub fn safePath() void {
        \\    var visit: Visit = .{};
        \\    visitArtifacts(&visit, Visit.visit, 0);
        \\}
    );
}
test "optional callback: direct dispatcher rejects a wrong receiver type" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Visit = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\const Other = struct { value: usize = 0 };
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn unsafePath() void {
        \\    var other: Other = .{};
        \\    visitArtifacts(&other, Visit.visit);
        \\}
    );
}

test "optional callback: direct dispatcher preserves underalignment findings" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Visit = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn unsafePath(visit: *align(1) Visit) void {
        \\    visitArtifacts(visit, Visit.visit);
        \\}
    );
}

test "optional callback: direct dispatcher rejects a mutated context" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Visit = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    var selected = context;
        \\    selected = null;
        \\    callback(selected);
        \\}
        \\pub fn unsafePath() void {
        \\    var visit: Visit = .{};
        \\    visitArtifacts(&visit, Visit.visit);
        \\}
    );
}

test "optional callback: direct dispatcher does not close stored callbacks" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Visit = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\var stored: ?*const fn (?*anyopaque) void = null;
        \\pub fn retain(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    _ = context;
        \\    stored = callback;
        \\}
        \\pub fn unsafePath() void {
        \\    var visit: Visit = .{};
        \\    retain(&visit, Visit.visit);
        \\}
    );
}
test "optional callback: direct dispatcher keeps nullable context findings" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Visit = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn unsafePath() void {
        \\    visitArtifacts(null, Visit.visit);
        \\}
    );
}

test "optional callback: direct dispatcher does not pair a different callback" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct { value: usize = 0 };
        \\const Other = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Other = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn unsafePath() void {
        \\    var visit: Visit = .{};
        \\    visitArtifacts(&visit, Other.visit);
        \\}
    );
}

test "optional callback: direct dispatcher keeps pointer offset findings" {
    try testing.expectFiresTyped(check, R,
        \\const Visit = struct {
        \\    fn visit(context: ?*anyopaque) void {
        \\        const self: *Visit = @ptrCast(@alignCast(context.?));
        \\        _ = self;
        \\    }
        \\};
        \\fn visitArtifacts(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn unsafePath() void {
        \\    var visit: Visit = .{};
        \\    const displaced: *Visit = @ptrFromInt(@intFromPtr(&visit) + 1);
        \\    visitArtifacts(displaced, Visit.visit);
        \\}
    );
}

test "optional callback: canonical source and destination pointer aliases preserve alignment" {
    try testing.expectNoFireTyped(check,
        \\const State = struct {
        \\    calls: usize = 0,
        \\    const Pointer = *State;
        \\    fn onEvent(raw: ?*anyopaque) void {
        \\        const self: Pointer = @ptrCast(@alignCast(raw.?));
        \\        self.calls += 1;
        \\    }
        \\};
        \\const Alias = State.Pointer;
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
        \\fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
        \\pub fn run(state: Alias) void {
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: pointer aliases do not conflate structurally equal pointees" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct {
        \\    calls: usize = 0,
        \\    const Pointer = *State;
        \\    fn onEvent(raw: ?*anyopaque) void {
        \\        const self: Pointer = @ptrCast(@alignCast(raw.?));
        \\        self.calls += 1;
        \\    }
        \\};
        \\const Other = struct {
        \\    calls: usize = 0,
        \\    const Pointer = *Other;
        \\};
        \\const Alias = Other.Pointer;
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
        \\fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
        \\pub fn run(state: Alias) void {
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: namespace aliases retain const pointee identity" {
    try testing.expectNoFireTyped(check,
        \\const State = struct {
        \\    calls: usize = 0,
        \\    const Pointer = *const State;
        \\    fn onEvent(raw: ?*const anyopaque) void {
        \\        const self: Pointer = @ptrCast(@alignCast(raw.?));
        \\        _ = self.calls;
        \\    }
        \\};
        \\const Namespace = struct { const Alias = State.Pointer; };
        \\const Callback = struct { context: ?*const anyopaque, invoke: *const fn (?*const anyopaque) void };
        \\fn dispatch(callback: Callback) void { callback.invoke(callback.context); }
        \\pub fn run(state: Namespace.Alias) void {
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: canonical aliases retain underalignment and allowzero boundaries" {
    try testing.expectFiresTyped(check, R, pointer_fixture ++
        \\const Alias = *align(1) State;
        \\pub fn run(state: Alias) void {
        \\    dispatch(.{ .context = state, .invoke = State.onEvent });
        \\}
    );
    try testing.expectFiresTyped(check, R, pointer_fixture ++
        \\const Alias = *allowzero State;
        \\pub fn run(state: Alias) void {
        \\    dispatch(.{ .context = @ptrCast(state), .invoke = State.onEvent });
        \\}
    );
}

test "optional callback: destination aliases do not discard stronger explicit alignment" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct { calls: usize = 0 };
        \\const Alias = *align(64) State;
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
        \\fn callback(raw: ?*anyopaque) void {
        \\    const state: Alias = @ptrCast(@alignCast(raw.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(pair: Callback) void { pair.invoke(pair.context); }
        \\pub fn run(state: *State) void {
        \\    dispatch(.{ .context = state, .invoke = callback });
        \\}
    );
}

test "optional pointer: guarded canonical optional and pointer aliases match the target" {
    try testing.expectNoFireTyped(check,
        \\const State = struct { value: u32 };
        \\const Pointer = *State;
        \\const Optional = ?Pointer;
        \\fn recover(raw: Optional) !Pointer {
        \\    if (raw == null) return error.Missing;
        \\    return @alignCast(raw.?);
        \\}
    );
}

test "optional pointer: guarded aliases do not conflate structurally equal pointees" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct { value: u32 };
        \\const Other = struct { value: u32 };
        \\const Pointer = *State;
        \\const Optional = ?*Other;
        \\fn recover(raw: Optional) !Pointer {
        \\    if (raw == null) return error.Missing;
        \\    return @ptrCast(@alignCast(raw.?));
        \\}
    );
}

test "optional pointer: null rejection cannot repair an underaligned pointer alias" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct { value: u32 };
        \\const Pointer = *align(1) State;
        \\const Optional = ?Pointer;
        \\fn recover(raw: Optional) !*State {
        \\    if (raw == null) return error.Missing;
        \\    return @alignCast(raw.?);
        \\}
    );
}

test "optional callback: direct dispatch retains a source proved typed allocation" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const State = struct {
        \\    value: u32 = 0,
        \\    fn callback(raw: ?*anyopaque) void {
        \\        const self: *State = @ptrCast(@alignCast(raw.?));
        \\        self.value += 1;
        \\    }
        \\};
        \\fn visit(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn run(allocator: std.mem.Allocator) !void {
        \\    const state = try allocator.create(State);
        \\    defer allocator.destroy(state);
        \\    state.* = .{};
        \\    visit(state, State.callback);
        \\}
    );
}

test "optional callback: direct dispatch does not authenticate an opaque pointer factory" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct {
        \\    value: u32 = 0,
        \\    fn callback(raw: ?*anyopaque) void {
        \\        const self: *State = @ptrCast(@alignCast(raw.?));
        \\        self.value += 1;
        \\    }
        \\};
        \\extern fn acquire() *State;
        \\fn visit(context: ?*anyopaque, callback: *const fn (?*anyopaque) void) void {
        \\    callback(context);
        \\}
        \\pub fn run() void {
        \\    const state = acquire();
        \\    visit(state, State.callback);
        \\}
    );
}
