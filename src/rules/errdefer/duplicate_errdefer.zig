//! tigerbeetle/tigerbeetle#2700 detector — two `errdefer
//! <X>.<cleanup>();` statements in one fn body that register the
//! same cleanup against the same receiver.  On error both fire and
//! the cleanup runs twice → double-free / assert.
//!
//! Detection (per function):
//!   1. Collect inline errdefer calls in their lexical block.
//!   2. Compare the complete call and each lexical root declaration.
//!   3. Equal numeric amounts alone do not identify one resource.
//!      Typed scalar-only argument calls therefore supply no duplicate
//!      certificate; equal receiver paths and resource arguments retain
//!      the check. Deferred mutable paths are read at exit, not captured
//!      at registration.
//!
//! Skip outer comptime type-builders so nested-fn errdefers aren't
//! double-counted via the wrapping fn.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const returnsType = tokens.returnsType;
const skipFnDecl = tokens.skipFnDecl;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .duplicate_errdefer)) return;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();

    var node_idx: u32 = 1;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        const body = bodyOf(tree, node) orelse continue;
        const proto = tokens.fnProto(tree, &proto_buffer, node) orelse continue;
        const bindings = (try cache.localBindings(proto, body)).*;
        try checkBody(gpa, tree, cache, &bindings, body, problems);
    }
}

const Cleanup = struct {
    /// Token of the `errdefer` keyword — used as diagnostic anchor.
    errdefer_tok: Ast.TokenIndex,
    /// First token (inclusive) of the full `<recv>.<method>(<args>)`
    /// call — covers receiver chain + method + every argument.
    /// Comparing this range token-for-token (rather than just
    /// receiver + method) keeps `allocator.free(a)` vs
    /// `allocator.free(b)` distinct — same method, same receiver,
    /// different args.
    call_first: Ast.TokenIndex,
    /// Last token (inclusive) of the full call expression — the
    /// closing `)`.
    call_last: Ast.TokenIndex,
    /// Token index of the IMMEDIATE enclosing `{` — the open-brace
    /// of the block this errdefer lives in.  Two errdefers in
    /// DIFFERENT enclosing braces are typically in mutually
    /// exclusive branches (`if {...} else if {...}`); both can't
    /// register at runtime so there's no double-free risk.
    enclosing_lbrace: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var entries: std.ArrayListUnmanaged(Cleanup) = .empty;
    defer entries.deinit(gpa);

    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        // Skip past nested fns so their errdefers stay scoped.
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_errdefer) continue;
        // Inline form: `errdefer <recv-chain>.<method>(...);`.
        var e = parseInlineErrdefer(tree, t, last) orelse continue;
        e.enclosing_lbrace = findEnclosingLBrace(tags, t, first);
        try entries.append(gpa, e);
    }

    if (entries.items.len < 2) return;

    // Pairwise compare full-call token ranges.  Fire on the SECOND
    // occurrence of each duplicate so the earliest registration is
    // left as the "intended" one.
    for (entries.items, 0..) |a, i| {
        for (entries.items[0..i]) |b| {
            if (!callsEqual(tree, bindings, a, b)) continue;
            // Equal numeric amounts name no resource. Repeated accounting
            // debits can discharge separate successful acquisitions.
            if (try hasOnlyScalarArguments(cache, a)) continue;
            // Branch-disjoint guard: two errdefers in different
            // immediate scopes (different `{`s) are typically in
            // mutually exclusive arms of an `if/else if/else`
            // chain — only one ever registers, so no double-free.
            // Same-scope duplicates are the real bug.
            if (a.enclosing_lbrace != b.enclosing_lbrace) continue;
            try report(gpa, problems, tree, a, b);
            break;
        }
    }
}

/// Parse `errdefer <recv-chain>.<method>(<args>);` immediately
/// following the `errdefer` keyword at `ed_tok`.  Captures the
/// FULL call (receiver + method + args) so later comparison can
/// reject `allocator.free(a)` vs `allocator.free(b)` as distinct
/// cleanups.  Returns null when the shape doesn't match (block
/// form, no method call, no method-with-call shape, etc.).
fn parseInlineErrdefer(tree: *const Ast, ed_tok: Ast.TokenIndex, last: Ast.TokenIndex) ?Cleanup {
    const tags = tree.tokens.items(.tag);
    if (ed_tok + 1 > last) return null;
    if (tags[ed_tok + 1] != .identifier) return null;
    var t: Ast.TokenIndex = ed_tok + 1;
    var ident_count: u32 = 0;
    var last_paren_end: ?Ast.TokenIndex = null;
    // Walk a chain of `<ident>(.<ident>)*` with optional `()` after
    // each segment (e.g. `dev.allocator().free(arg)`).  After each
    // `()` group, keep extending if the next token is `.`.  The
    // FINAL call's closing paren is what call_last must point to —
    // otherwise two errdefers that share only the first segment
    // (`dev.allocator()`) get matched as duplicates even when the
    // tail differs (`free(specifier_cloned)` vs `free(dir_name)`).
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .identifier => ident_count += 1,
            .period => {},
            .l_paren => {
                var depth: u32 = 1;
                var u: Ast.TokenIndex = t + 1;
                while (u <= last and depth > 0) : (u += 1) {
                    switch (tags[u]) {
                        .l_paren => depth += 1,
                        .r_paren => depth -= 1,
                        else => {},
                    }
                }
                if (depth != 0) return null;
                last_paren_end = u - 1;
                // Continue if a chained method follows: `.<ident>...`.
                if (u <= last and tags[u] == .period) {
                    t = u; // advance to `.`; outer loop will continue
                    continue;
                }
                break;
            },
            else => return null,
        }
    }
    const call_end = last_paren_end orelse return null;
    if (ident_count < 2) return null;
    return .{
        .errdefer_tok = ed_tok,
        .call_first = ed_tok + 1,
        .call_last = call_end,
        .enclosing_lbrace = 0,
    };
}

/// Walk back from the `errdefer` token through the fn body, tracking
/// brace depth.  The first `{` at depth -1 is the immediate enclosing
/// open-brace.  Bounded by `lo` (fn body's first token) so we never
/// stray outside.
fn findEnclosingLBrace(
    tags: []const std.zig.Token.Tag,
    ed_tok: Ast.TokenIndex,
    lo: Ast.TokenIndex,
) Ast.TokenIndex {
    var depth: i32 = 0;
    var t: Ast.TokenIndex = ed_tok;
    while (t > lo) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) return t;
                depth -= 1;
            },
            else => {},
        }
    }
    return lo;
}

fn callsEqual(tree: *const Ast, bindings: *const local_bindings.LocalBindings, a: Cleanup, b: Cleanup) bool {
    const tags = tree.tokens.items(.tag);
    const a_len = a.call_last - a.call_first;
    const b_len = b.call_last - b.call_first;
    if (a_len != b_len) return false;
    var i: usize = 0;
    while (i <= a_len) : (i += 1) {
        const ai = a.call_first + @as(Ast.TokenIndex, @intCast(i));
        const bi = b.call_first + @as(Ast.TokenIndex, @intCast(i));
        if (tags[ai] != tags[bi]) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(ai), tree.tokenSlice(bi))) return false;
        if (tags[ai] == .identifier and
            (ai == a.call_first or tags[ai - 1] != .period))
        {
            const a_binding = bindings.findAt(tree.tokenSlice(ai), ai);
            const b_binding = bindings.findAt(tree.tokenSlice(bi), bi);
            if (a_binding != null and b_binding != null and
                a_binding.?.name_token != b_binding.?.name_token) return false;
            if ((a_binding == null) != (b_binding == null)) return false;
        }
    }
    return true;
}

fn hasOnlyScalarArguments(cache: *file_cache_mod.FileCache, cleanup: Cleanup) file_cache_mod.SummaryError!bool {
    const resolver = cache.zls orelse return false;
    const tree = cache.tree;
    const node = cache.nodeForExactSpan(cleanup.call_first, cleanup.call_last) orelse return false;
    try cache.chargeNormalCleanup(node);
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    if (call.ast.params.len == 0) return false;
    for (call.ast.params) |argument| {
        const actual = (try resolver.resolutionFrame().typeOfNode(argument)) orelse return false;
        switch (resolver.typeTag(actual) orelse return false) {
            .int, .comptime_int, .float, .comptime_float => {},
            else => return false,
        }
    }
    return true;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    dup: Cleanup,
    earlier: Cleanup,
) !void {
    const starts = tree.tokens.items(.start);
    const call_start = starts[dup.call_first];
    const call_end = starts[dup.call_last] + tree.tokenSlice(dup.call_last).len;
    const call_text = tree.source[call_start..call_end];

    const earlier_loc = tree.tokenLocation(0, earlier.errdefer_tok);
    const earlier_line: u32 = @intCast(earlier_loc.line + 1);

    const msg = try std.fmt.allocPrint(
        gpa,
        "`errdefer {s};` is already registered earlier in this fn (line {d}) — on the error path both fire, running the same cleanup twice (double-free / assert).  Remove this duplicate registration",
        .{ call_text, earlier_line },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "duplicate-errdefer",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, dup.errdefer_tok),
        .end = try Pos.fromTokenEnd(tree, dup.errdefer_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "duplicate-errdefer: two identical `errdefer X.deinit()` fires once" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const IO = struct { pub fn init() !IO { return .{}; } pub fn deinit(_: *IO) void {} };
        \\const Cmd = struct {
        \\    io: IO = .{},
        \\    pub fn init(this: *Cmd) !void {
        \\        this.io = try IO.init();
        \\        errdefer this.io.deinit();
        \\        this.io = try IO.init();
        \\        errdefer this.io.deinit();
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("duplicate-errdefer", problems.items[0].rule_id);
}

test "duplicate-errdefer: distinct receivers don't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct { pub fn deinit(_: *T) void {} };
        \\const S = struct {
        \\    a: T = .{},
        \\    b: T = .{},
        \\    pub fn init(this: *S) !void {
        \\        errdefer this.a.deinit();
        \\        errdefer this.b.deinit();
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "duplicate-errdefer: same receiver, different methods don't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct {
        \\    pub fn deinit(_: *T) void {}
        \\    pub fn close(_: *T) void {}
        \\};
        \\const S = struct {
        \\    handle: T = .{},
        \\    pub fn init(this: *S) !void {
        \\        errdefer this.handle.deinit();
        \\        errdefer this.handle.close();
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "duplicate-errdefer: bare local receiver fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct { pub fn deinit(_: *T) void {} };
        \\pub fn doStuff() !void {
        \\    var x: T = .{};
        \\    errdefer x.deinit();
        \\    errdefer x.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "duplicate-errdefer: mutually exclusive if/else if branches don't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct { pub fn deinit(_: *T, _: anytype) void {} };
        \\pub fn parse(allocator: anytype, a: ?u32, b: ?u32) !void {
        \\    if (a) |_| {
        \\        var x: T = .{};
        \\        errdefer x.deinit(allocator);
        \\        _ = x;
        \\    } else if (b) |_| {
        \\        var x: T = .{};
        \\        errdefer x.deinit(allocator);
        \\        _ = x;
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "duplicate-errdefer: nested fn errdefers don't bleed into outer scan" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const T = struct { pub fn deinit(_: *T) void {} };
        \\pub fn outer() void {
        \\    const Inner = struct {
        \\        pub fn run() !void {
        \\            var x: T = .{};
        \\            errdefer x.deinit();
        \\            errdefer x.deinit();
        \\        }
        \\    };
        \\    _ = Inner;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Inner fires once; outer skips past inner's body.
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "duplicate-errdefer: scalar accounting is not a resource identity" {
    try testing.expectNoFireTyped(check,
        \\const Ledger = struct {
        \\    context: *anyopaque,
        \\    acquire_fn: *const fn (*anyopaque, usize) anyerror!void,
        \\    release_fn: *const fn (*anyopaque, usize) void,
        \\    fn acquire(self: *Ledger, count: usize) !void { return self.acquire_fn(self.context, count); }
        \\    fn release(self: *Ledger, count: usize) void { self.release_fn(self.context, count); }
        \\};
        \\pub fn build(ledger: *Ledger, count: usize) !void {
        \\    try ledger.acquire(count);
        \\    errdefer ledger.release(count);
        \\    try ledger.acquire(count);
        \\    errdefer ledger.release(count);
        \\    try later();
        \\}
        \\fn later() !void {}
    );
}

test "duplicate-errdefer: pointer resource argument still identifies duplicate cleanup" {
    try testing.expectFiresTyped(check, "duplicate-errdefer",
        \\const Allocator = struct { fn free(_: Allocator, _: []u8) void {} };
        \\pub fn build(allocator: Allocator, bytes: []u8) !void {
        \\    errdefer allocator.free(bytes);
        \\    errdefer allocator.free(bytes);
        \\    return error.Later;
        \\}
    );
}

test "duplicate-errdefer: deferred receivers read the rebound path on exit" {
    try testing.expectFiresTyped(check, "duplicate-errdefer",
        \\const Handle = struct { fn close(_: Handle) void {} };
        \\pub fn build(first: Handle, second: Handle) !void {
        \\    var handle = first;
        \\    errdefer handle.close();
        \\    handle = second;
        \\    errdefer handle.close();
        \\    return error.Later;
        \\}
    );
}

test "duplicate-errdefer: value snapshots and branch captures stay distinct" {
    try testing.expectNoFireTyped(check,
        \\const Handle = struct { fn close(_: Handle) void {} };
        \\pub fn build(first: Handle, second: Handle) !void {
        \\    var handle = first;
        \\    const saved = handle;
        \\    errdefer saved.close();
        \\    handle = second;
        \\    errdefer handle.close();
        \\    return error.Later;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Handle = struct { fn close(_: Handle) void {} };
        \\pub fn build(first: ?Handle, second: ?Handle) !void {
        \\    if (first) |held| { errdefer held.close(); }
        \\    if (second) |held| { errdefer held.close(); }
        \\    return error.Later;
        \\}
    );
}
