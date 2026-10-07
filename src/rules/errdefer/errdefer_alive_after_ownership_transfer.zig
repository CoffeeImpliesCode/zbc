//! Detects cleanup that remains armed after a proven ownership transfer
//! and can run again when a subsequent `try` propagates an error.
//!
//! Transfer evidence comes from the exact AST call's canonical callee
//! summary, mapped from the consumed formal to its actual argument.
//! A constructor name or storage of a borrowed pointer is not proof.
//! Fallible arguments are evaluated before the call takes ownership.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "errdefer-alive-after-ownership-transfer";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .errdefer_alive_after_ownership_transfer)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkBody);
}

const Armed = struct {
    x_name: []const u8,
    /// First token AFTER the errdefer's closing `)`.
    scan_from: Ast.TokenIndex,
    scope_last: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    _: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Collect all errdefer X.cleanup() registrations.
    var armed: std.ArrayListUnmanaged(Armed) = .empty;
    defer armed.deinit(gpa);

    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_errdefer) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .period) continue;
        if (tags[t + 3] != .identifier) continue;
        if (!isCleanupName(tree.tokenSlice(t + 3))) continue;
        if (tags[t + 4] != .l_paren) continue;
        if (tags[t + 5] != .r_paren) continue;

        try armed.append(gpa, .{
            .x_name = tree.tokenSlice(t + 1),
            .scan_from = t + 6,
            .scope_last = cleanupScopeEnd(tags, t + 6, last),
        });
    }

    if (armed.items.len == 0) return;

    for (armed.items) |a| {
        if (a.scan_from > last) continue;

        // Only the actual callee's ownership contract can consume X.
        const transfer_end = (try findOwnershipCall(
            tree,
            cache,
            tags,
            a.scan_from,
            a.scope_last,
            a.x_name,
        )) orelse continue;

        // Scan from transfer_end forward for a `try` before `X = `.
        const danger_try = findTryBeforeDisarm(
            tree,
            tags,
            transfer_end,
            a.scope_last,
            a.x_name,
        ) orelse continue;

        try report(gpa, problems, tree, danger_try, a.x_name);
    }
}

fn isCleanupName(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "deref") or
        std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "close") or
        std.mem.eql(u8, name, "destroy");
}

/// An errdefer expires on successful exit from its registering block.
fn cleanupScopeEnd(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
) Ast.TokenIndex {
    var depth: u32 = 0;
    var t = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => {
                if (depth == 0) return t;
                depth -= 1;
            },
            else => {},
        }
    }
    return last;
}

/// Returns the first token after a proven transfer, before X is disarmed.
fn findOwnershipCall(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    x_name: []const u8,
) !?Ast.TokenIndex {
    const calls = try cache.getCallIndex();
    var t: Ast.TokenIndex = start;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = tokens.skipDeferStmt(tags, t, last) orelse return null;
            continue;
        }
        if (tags[t] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t), x_name) and
            t + 1 <= last and tags[t + 1] == .equal)
            return null;

        const node = calls.by_callee_token.get(t) orelse continue;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, node) orelse continue;
        const record = (try cache.actualCallSummaryAt(
            fresh_storage.calleeQueryToken(tree, call),
            null,
        )) orelse continue;
        // The call record carries declaration facts by default. This rule
        // needs definite normal-success release and retained ownership, so
        // request those outcomes for the same canonical instantiated callee.
        const summary = (try cache.summaryOfResolvedMethod(record.callee)) orelse continue;
        const immediate = summary.normal_success_definite_freed_paths;
        const retained = summary.retained_owned_params;
        for (0..immediate.len + retained.len) |owned_index| {
            const parameter = if (owned_index < immediate.len) parameter: {
                const released = immediate[owned_index];
                if (released.path.len != 0) continue;
                break :parameter released.param;
            } else retained[owned_index - immediate.len];
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try record.callArgumentFor(
                cache,
                &argument_buffer,
                parameter,
            )) orelse continue;
            if (tree.nodeTag(argument) != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(argument)), x_name)) continue;
            return tree.lastToken(node) + 1;
        }
    }
    return null;
}

/// Scans [start, last] for `keyword_try` before `identifier(x_name) equal`.
/// Returns the `keyword_try` token index, or null if x_name is disarmed first.
fn findTryBeforeDisarm(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    x_name: []const u8,
) ?Ast.TokenIndex {
    var t: Ast.TokenIndex = start;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = tokens.skipDeferStmt(tags, t, last) orelse return null;
            continue;
        }

        // Disarming assignment: x_name = ...
        if (tags[t] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t), x_name) and
            t + 1 <= last and tags[t + 1] == .equal)
            return null; // disarmed

        if (tags[t] == .keyword_try) return t;
    }
    return null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    try_tok: Ast.TokenIndex,
    x_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`errdefer {s}.deinit()` is still armed after a proven ownership transfer of `{s}` — if this `try` propagates an error, the errdefer fires and double-frees `{s}`; reset `{s}` to an appropriate inert sentinel immediately after the ownership-taking call to disarm the errdefer",
        .{ x_name, x_name, x_name, x_name },
    );
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

const testResourceSource =
    \\const std = @import("std");
    \\const Resource = struct {
    \\    bytes: ?[]u8 = null,
    \\    pub fn deinit(self: *Resource) void {
    \\        if (self.bytes) |bytes| std.heap.page_allocator.free(bytes);
    \\    }
    \\};
    \\fn discard(gpa: std.mem.Allocator, resource: *Resource) void {
    \\    resource.deinit();
    \\    gpa.destroy(resource);
    \\}
    \\fn later() !void { return error.Later; }
    \\fn path() ![]const u8 { return "fixture.zig"; }
    \\
;

test "errdefer-alive-after-ownership-transfer: init stores borrowed context only" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\const Resolver = struct {
        \\    context: ?*Resource = null,
        \\    scratch: ?[]u8 = null,
        \\    pub fn init(self: *Resolver, context: *Resource,
        \\        gpa: std.mem.Allocator, name: []const u8) !void {
        \\        self.context = context;
        \\        self.scratch = try gpa.dupe(u8, name);
        \\    }
        \\    pub fn deinit(self: *Resolver, gpa: std.mem.Allocator) void {
        \\        if (self.scratch) |scratch| gpa.free(scratch);
        \\    }
        \\};
        \\fn open(gpa: std.mem.Allocator, context: *Resource) !void {
        \\    errdefer context.deinit();
        \\    var resolver: Resolver = .{};
        \\    try resolver.init(context, gpa, try path());
        \\    errdefer resolver.deinit(gpa);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: foreign resolver borrows context" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    const type_engine = @import("type_engine");
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "resolver.zig", .data =
        \\const std = @import("std");
        \\pub const Context = struct {
        \\    bytes: ?[]u8 = null,
        \\    pub fn deinit(self: *Context) void {
        \\        if (self.bytes) |bytes| std.heap.page_allocator.free(bytes);
        \\    }
        \\};
        \\pub const Resolver = struct {
        \\    context: *Context,
        \\    allocator: std.mem.Allocator,
        \\    path: []u8,
        \\    source: []u8,
        \\    pub fn init(self: *Resolver, context: *Context,
        \\        allocator: std.mem.Allocator, path: []const u8,
        \\        source: []const u8) !void {
        \\        const owned_path = try allocator.dupe(u8, path);
        \\        errdefer allocator.free(owned_path);
        \\        const owned_source = try allocator.dupe(u8, source);
        \\        self.context = context;
        \\        self.allocator = allocator;
        \\        self.path = owned_path;
        \\        self.source = owned_source;
        \\    }
        \\    pub fn deinit(self: *Resolver) void {
        \\        self.allocator.free(self.path);
        \\        self.allocator.free(self.source);
        \\    }
        \\};
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const source =
        \\const std = @import("std");
        \\const foreign = @import("resolver.zig");
        \\fn path() ![]const u8 { return "/tmp/fixture.zig"; }
        \\fn later() !void { return error.Later; }
        \\fn open(gpa: std.mem.Allocator, context: *foreign.Context) !void {
        \\    errdefer context.deinit();
        \\    var resolver: foreign.Resolver = undefined;
        \\    try resolver.init(context, gpa, try path(), "fn f() void {}");
        \\    errdefer resolver.deinit();
        \\    try later();
        \\}
    ;
    // Admit this fixture's foreign source only. Explicit exclusion must
    // still refuse that same import, rather than quietly claiming no hazard.
    for ([_]bool{ false, true }) |excluded| {
        var context: type_engine.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{
            .roots = &.{directory},
            .excludes = if (excluded) &.{"resolver.zig"} else &.{},
        };
        var resolver: type_engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, path, source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
        var cache = file_cache_mod.FileCache.init(gpa, tree);
        cache.setZls(&resolver);
        defer cache.deinit();
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer testing.freeProblems(gpa, &problems);
        if (excluded) {
            try std.testing.expectError(error.SourceExcluded, check(gpa, tree, &cache, &config_mod.Default, &problems));
        } else {
            try check(gpa, tree, &cache, &config_mod.Default, &problems);
            try std.testing.expectEqual(@as(usize, 0), problems.items.len);
        }
    }
}

test "errdefer-alive-after-ownership-transfer: proven nonconstructor consume fires" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    discard(gpa, resource);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: retained field with owning cleanup fires" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Owner = struct {
        \\    gpa: std.mem.Allocator,
        \\    resource: *Resource,
        \\    pub fn init(gpa: std.mem.Allocator, resource: *Resource) Owner {
        \\        return .{ .gpa = gpa, .resource = resource };
        \\    }
        \\    pub fn deinit(self: *Owner) void {
        \\        self.resource.deinit();
        \\        self.gpa.destroy(self.resource);
        \\    }
        \\};
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    var owner = Owner.init(gpa, resource);
        \\    defer owner.deinit();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: implicit method formal mapping" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Sink = struct {
        \\    gpa: std.mem.Allocator,
        \\    pub fn accept(self: *Sink, tag: u32, resource: *Resource) void {
        \\        _ = tag;
        \\        resource.deinit();
        \\        self.gpa.destroy(resource);
        \\    }
        \\};
        \\fn open(sink: *Sink, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    sink.accept(7, resource);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: explicit method formal mapping" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Sink = struct {
        \\    gpa: std.mem.Allocator,
        \\    pub fn accept(self: *Sink, tag: u32, resource: *Resource) void {
        \\        _ = tag;
        \\        resource.deinit();
        \\        self.gpa.destroy(resource);
        \\    }
        \\};
        \\fn open(sink: *Sink, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    Sink.accept(sink, 7, resource);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: another formal consumed leaves cleanup valid" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn accept(gpa: std.mem.Allocator, borrowed: *Resource, owned: *Resource) void {
        \\    _ = borrowed.bytes;
        \\    owned.deinit();
        \\    gpa.destroy(owned);
        \\}
        \\fn open(gpa: std.mem.Allocator, context: *Resource, owned: *Resource) !void {
        \\    errdefer context.deinit();
        \\    accept(gpa, context, owned);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: same spelled actual declarations differ" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Borrow = struct {
        \\    pub fn init(resource: *Resource) void { _ = resource.bytes; }
        \\};
        \\const Consume = struct {
        \\    pub fn init(gpa: std.mem.Allocator, resource: *Resource) void {
        \\        resource.deinit();
        \\        gpa.destroy(resource);
        \\    }
        \\};
        \\fn borrow(context: *Resource) !void {
        \\    errdefer context.deinit();
        \\    Borrow.init(context);
        \\    try later();
        \\}
        \\fn consume(gpa: std.mem.Allocator, context: *Resource) !void {
        \\    errdefer context.deinit();
        \\    Consume.init(gpa, context);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: unresolved prototype is not proof" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\extern fn constructWidget(resource: *Resource) void;
        \\fn open(resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    constructWidget(resource);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: unknown function pointer is not proof" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(resource: *Resource, init: *const fn (*Resource) void) !void {
        \\    errdefer resource.deinit();
        \\    init(resource);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: disarm after proven consume" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, original: *Resource) !void {
        \\    var empty: Resource = .{};
        \\    var resource = original;
        \\    errdefer resource.deinit();
        \\    discard(gpa, resource);
        \\    resource = &empty;
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: disarm before consume" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, original: *Resource) !void {
        \\    var empty: Resource = .{};
        \\    var resource = original;
        \\    errdefer resource.deinit();
        \\    resource = &empty;
        \\    discard(gpa, original);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: no later try after proven consume" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    discard(gpa, resource);
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: fallible argument precedes consume" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn accept(gpa: std.mem.Allocator, resource: *Resource, name: []const u8) void {
        \\    _ = name;
        \\    resource.deinit();
        \\    gpa.destroy(resource);
        \\}
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    accept(gpa, resource, try path());
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: nested function try is not executed" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    discard(gpa, resource);
        \\    const Nested = struct {
        \\        fn work() !void { try later(); }
        \\    };
        \\    _ = Nested;
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: cleanup expires before outer try" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    {
        \\        errdefer resource.deinit();
        \\        discard(gpa, resource);
        \\    }
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: later nested block try keeps cleanup armed" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    discard(gpa, resource);
        \\    {
        \\        try later();
        \\    }
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: implicit consumed receiver maps formal zero" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Sink = struct {
        \\    gpa: std.mem.Allocator,
        \\    pub fn deinit(self: *Sink) void { self.gpa.destroy(self); }
        \\    pub fn finish(self: *Sink) void { self.gpa.destroy(self); }
        \\};
        \\fn open(sink: *Sink) !void {
        \\    errdefer sink.deinit();
        \\    sink.finish();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: explicit consumed receiver maps formal zero" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Sink = struct {
        \\    gpa: std.mem.Allocator,
        \\    pub fn deinit(self: *Sink) void { self.gpa.destroy(self); }
        \\    pub fn finish(self: *Sink) void { self.gpa.destroy(self); }
        \\};
        \\fn open(sink: *Sink) !void {
        \\    errdefer sink.deinit();
        \\    Sink.finish(sink);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: retained receiver field with owning cleanup" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Owner = struct {
        \\    gpa: std.mem.Allocator,
        \\    resource: ?*Resource = null,
        \\    pub fn init(self: *Owner, resource: *Resource) void {
        \\        self.resource = resource;
        \\    }
        \\    pub fn deinit(self: *Owner) void {
        \\        if (self.resource) |resource| {
        \\            resource.deinit();
        \\            self.gpa.destroy(resource);
        \\        }
        \\    }
        \\};
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    var owner: Owner = .{ .gpa = gpa };
        \\    owner.init(resource);
        \\    defer owner.deinit();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: deferred consume has not run" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    defer discard(gpa, resource);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: deferred assignment does not disarm" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\fn open(gpa: std.mem.Allocator, original: *Resource) !void {
        \\    var empty: Resource = .{};
        \\    var resource = original;
        \\    errdefer resource.deinit();
        \\    defer resource = &empty;
        \\    discard(gpa, resource);
        \\    try later();
        \\}
        \\
    );
}

const testRetainedPairSource = testResourceSource ++
    \\const PairOwner = struct {
    \\    gpa: std.mem.Allocator,
    \\    first: *Resource,
    \\    second: *Resource,
    \\    pub fn init(self: *PairOwner, borrowed: *Resource,
    \\        first: *Resource, second: *Resource) void {
    \\        _ = borrowed.bytes;
    \\        self.first = first;
    \\        self.second = second;
    \\    }
    \\    pub fn deinit(self: *PairOwner) void {
    \\        self.first.deinit();
    \\        self.second.deinit();
    \\        self.gpa.destroy(self.first);
    \\        self.gpa.destroy(self.second);
    \\    }
    \\};
    \\
;

test "errdefer-alive-after-ownership-transfer: second retained formal implicit method" {
    try testing.expectFiresTyped(check, R, testRetainedPairSource ++
        \\fn open(owner: *PairOwner, resource: *Resource,
        \\    other: *Resource, borrowed: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    owner.init(borrowed, other, resource);
        \\    defer owner.deinit();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: second retained formal explicit method" {
    try testing.expectFiresTyped(check, R, testRetainedPairSource ++
        \\fn open(owner: *PairOwner, resource: *Resource,
        \\    other: *Resource, borrowed: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    PairOwner.init(owner, borrowed, other, resource);
        \\    defer owner.deinit();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: retained other formals leave borrow armed" {
    try testing.expectNoFireTyped(check, testRetainedPairSource ++
        \\fn open(owner: *PairOwner, context: *Resource,
        \\    first: *Resource, second: *Resource) !void {
        \\    errdefer context.deinit();
        \\    owner.init(context, first, second);
        \\    defer owner.deinit();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: retained formal follows another immediate take" {
    try testing.expectFiresTyped(check, R, testResourceSource ++
        \\const Owner = struct {
        \\    gpa: std.mem.Allocator,
        \\    resource: *Resource,
        \\    pub fn init(gpa: std.mem.Allocator, temporary: *Resource,
        \\        resource: *Resource) Owner {
        \\        temporary.deinit();
        \\        gpa.destroy(temporary);
        \\        return .{ .gpa = gpa, .resource = resource };
        \\    }
        \\    pub fn deinit(self: *Owner) void {
        \\        self.resource.deinit();
        \\        self.gpa.destroy(self.resource);
        \\    }
        \\};
        \\fn open(gpa: std.mem.Allocator, resource: *Resource, temporary: *Resource) !void {
        \\    errdefer resource.deinit();
        \\    var owner = Owner.init(gpa, temporary, resource);
        \\    defer owner.deinit();
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: conditional free is not definite transfer" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn init(gpa: std.mem.Allocator, resource: *Resource, release: bool) void {
        \\    if (release) {
        \\        resource.deinit();
        \\        gpa.destroy(resource);
        \\    }
        \\}
        \\fn open(gpa: std.mem.Allocator, resource: *Resource, release: bool) !void {
        \\    errdefer resource.deinit();
        \\    init(gpa, resource, release);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: free on error return is not normal transfer" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn init(gpa: std.mem.Allocator, resource: *Resource, fail: bool) !void {
        \\    if (fail) {
        \\        resource.deinit();
        \\        gpa.destroy(resource);
        \\        return error.Init;
        \\    }
        \\}
        \\fn open(gpa: std.mem.Allocator, resource: *Resource, fail: bool) !void {
        \\    errdefer resource.deinit();
        \\    try init(gpa, resource, fail);
        \\    try later();
        \\}
        \\
    );
}

test "errdefer-alive-after-ownership-transfer: errdefer free is not normal transfer" {
    try testing.expectNoFireTyped(check, testResourceSource ++
        \\fn init(gpa: std.mem.Allocator, resource: *Resource, fail: bool) !void {
        \\    errdefer {
        \\        resource.deinit();
        \\        gpa.destroy(resource);
        \\    }
        \\    if (fail) return error.Init;
        \\}
        \\fn open(gpa: std.mem.Allocator, resource: *Resource, fail: bool) !void {
        \\    errdefer resource.deinit();
        \\    try init(gpa, resource, fail);
        \\    try later();
        \\}
        \\
    );
}
