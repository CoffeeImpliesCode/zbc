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
            typedParameterMatchesTarget(tree, proto, t, tree.tokenSlice(t + 2))) continue;
        if (try callback_provenance.callbackParameterProven(cache, proto, t)) continue;

        try report(gpa, problems, tree, t);
    }
}

/// A null guard does not validate an opaque or explicitly underaligned
/// address. Only the same ordinary typed pointee is known aligned here.
fn typedParameterMatchesTarget(tree: *const Ast, proto: Ast.full.FnProto, cast: Ast.TokenIndex, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    var source: ?[]const u8 = null;
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        const nt = param.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), name)) continue;
        const node = param.type_expr orelse return false;
        const first = tree.firstToken(node);
        const last = tree.lastToken(node);
        if (first + 2 != last or tags[first] != .question_mark or
            tags[first + 1] != .asterisk or tags[last] != .identifier or
            std.mem.eql(u8, tree.tokenSlice(last), "anyopaque")) return false;
        source = tree.tokenSlice(last);
    }
    const pointee = source orelse return false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const decl = tree.fullVarDecl(node) orelse continue;
        const init = decl.ast.init_node.unwrap() orelse continue;
        if (tree.firstToken(init) > cast or tree.lastToken(init) < cast) continue;
        const target = decl.ast.type_node.unwrap() orelse return false;
        const first = tree.firstToken(target);
        const last = tree.lastToken(target);
        return first + 1 == last and tags[first] == .asterisk and
            std.mem.eql(u8, tree.tokenSlice(last), pointee);
    }
    // A direct return has the function's declared destination type.
    if (cast == 0 or tags[cast - 1] != .keyword_return) return false;
    const target = proto.ast.return_type.unwrap() orelse return false;
    const first = tree.firstToken(target);
    const last = tree.lastToken(target);
    return last > first and tags[last - 1] == .asterisk and
        std.mem.eql(u8, tree.tokenSlice(last), pointee);
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
    try testing.expectNoFire(check,
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
        ,
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
    cache.module_id = resolver.handle.module;
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
