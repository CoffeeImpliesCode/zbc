//! Advisory detector for raw-view and GC-dispatch method spellings.
//! The names alone establish neither a GC-managed buffer nor a GC effect.
//! Until ownership and dispatch are resolved, findings remain unknown
//! warnings: callers must check the actual lifetime contract.
//!
//! Real-world: oven-sh/bun#31339, multiple instances.
//!
//! For a confirmed JSC-managed view, its API may require:
//!   var pinned = buffer.pin(globalObject);
//!   defer pinned.unpin();
//!   const bytes = pinned.slice();
//!
//! Detection (Tier 3 — FileCache for FnSummary / body lookup):
//!   1. For each fn body, scan for `const/var NAME = recv.slice()` (or
//!      .utf8(), .latin1(), .utf16(), .utf16le(), .bytes(), .toSlice(),
//!      .toOwnedSlice(), .constSlice()) — a binding from a raw-view
//!      method spelling. Keep the full receiver path, not only its root.
//!   2. After that binding (token position), scan for either:
//!      a. A direct GC-trigger method call: any `any_recv.method(` where
//!         isGcTriggerMethodName(method) → fire directly.
//!      b. A bare function call `identifier(` where the callee is a
//!         same-file fn whose body calls a GC-trigger method.
//!   3. FP suppression: if a `.pin(` call on the SAME buffer receiver
//!      appears between the slice binding and the GC call, suppress.
//!   4. Fire at the GC-trigger call token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const matchBrace = tokens.matchBrace;
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipDeferStmt = tokens.skipDeferStmt;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const R = "arraybuffer-slice-without-pin";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .arraybuffer_slice_without_pin)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

/// Candidate raw-view spellings; names do not prove GC-managed storage.
fn isRawSliceMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "slice") or
        std.mem.eql(u8, name, "utf8") or
        std.mem.eql(u8, name, "latin1") or
        std.mem.eql(u8, name, "utf16") or
        std.mem.eql(u8, name, "utf16le") or
        std.mem.eql(u8, name, "bytes") or
        std.mem.eql(u8, name, "toSlice") or
        std.mem.eql(u8, name, "toOwnedSlice") or
        std.mem.eql(u8, name, "constSlice");
}

/// Candidate JSC dispatch spellings; names do not prove a GC effect.
fn isGcTriggerMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "call") or
        std.mem.eql(u8, name, "callAsFunction") or
        std.mem.eql(u8, name, "callAsConstructor") or
        std.mem.eql(u8, name, "construct") or
        std.mem.eql(u8, name, "execute") or
        std.mem.eql(u8, name, "runMicrotasks") or
        std.mem.eql(u8, name, "drainMicrotasks") or
        std.mem.eql(u8, name, "performMicrotaskCheckpoint") or
        std.mem.eql(u8, name, "collectGarbage") or
        std.mem.eql(u8, name, "gcProtect") or
        std.mem.eql(u8, name, "gcUnprotect") or
        std.mem.eql(u8, name, "toJS") or
        std.mem.eql(u8, name, "toJSValue") or
        std.mem.eql(u8, name, "resolve") or
        std.mem.eql(u8, name, "reject") or
        std.mem.eql(u8, name, "evaluate") or
        std.mem.eql(u8, name, "run") or
        std.mem.eql(u8, name, "handleException") or
        std.mem.eql(u8, name, "throwError") or
        std.mem.eql(u8, name, "throwException");
}

/// True iff `[first, last]` contains `.method(` where method is a GC
/// trigger name.  Skips nested fn bodies.
fn bodyMayInvokeGc(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (isGcTriggerMethodName(tree.tokenSlice(t + 1))) return true;
    }
    return false;
}

/// True iff the same-file top-level fn named `name` has a body that
/// calls a GC-trigger method.  Returns false on any lookup failure.
fn calleeBodyMayInvokeGc(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    name: []const u8,
) bool {
    const model = cache.fileModel() catch return false;
    const fi = model.findFn(name) orelse return false;
    const body = tokens.bodyOf(tree, fi.fn_decl) orelse return false;
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    return bodyMayInvokeGc(tree, first, last);
}

/// A raw-slice binding we're tracking.
const SliceBorrow = struct {
    x_name: []const u8,
    recv_first: Ast.TokenIndex,
    recv_last: Ast.TokenIndex,
    slice_method: []const u8,
    name_token: Ast.TokenIndex,
    /// Token index of the binding's terminating `;`.
    end_token: Ast.TokenIndex,
};

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const last = tree.lastToken(body);

    const bindings = try cache.localBindings(proto, body);

    var borrows: std.ArrayListUnmanaged(SliceBorrow) = .empty;
    defer borrows.deinit(gpa);

    // Collect raw-slice bindings from `const/var NAME = recv.method()`.
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        const ca = b.asCall() orelse continue;
        // method_call or try_method_call — needs a method field.
        const method = ca.method orelse continue;
        if (!isRawSliceMethodName(method)) continue;
        const recv = ca.receiver;
        if (recv.len == 0) continue;
        const method_token = ca.method_token orelse continue;
        if (method_token < ca.receiver_token + 2) continue;
        const receiver_last = method_token - 2;

        try borrows.append(gpa, .{
            .x_name = b.name,
            .recv_first = ca.receiver_token,
            .recv_last = receiver_last,
            .slice_method = method,
            .name_token = b.name_token,
            .end_token = b.rhs_last + 1,
        });
    }

    if (borrows.items.len == 0) return;

    // For each borrow, scan forward for a GC-triggering call.
    for (borrows.items) |b| {
        const scan_start = b.end_token + 1;
        if (scan_start > last) continue;
        const gc_tok = findGcTriggerCall(
            tree,
            cache,
            tags,
            scan_start,
            last,
            b,
        ) orelse continue;
        try reportProblem(gpa, problems, tree, b, gc_tok);
    }
}

/// Scan `[start, last]` at the fn's top scope for a GC-triggering call.
/// Stops at the scope's closing `}`.
/// Returns the token index of the GC trigger site (method name or bare
/// callee name), or null if none found.
/// Suppresses when `.pin(` is seen on the slice buffer receiver.
fn findGcTriggerCall(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    borrow: SliceBorrow,
) ?Ast.TokenIndex {
    if (start > last) return null;
    var t: Ast.TokenIndex = start;
    while (t + 1 <= last) : (t += 1) {
        // Skip nested function bodies.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Nested block → skip it (conditional execution; conservative).
        if (tags[t] == .l_brace) {
            t = matchBrace(tags, t, last) orelse return null;
            continue;
        }
        if (tags[t] == .r_brace) return null;
        // Skip defer/errdefer.
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = skipDeferStmt(tags, t, last) orelse return null;
            continue;
        }

        // Only a pin of this exact receiver path can protect its view.
        if (tags[t] == .identifier) {
            const receiver_len = borrow.recv_last - borrow.recv_first + 1;
            if (receiver_len <= last - t and last - t - receiver_len >= 2 and
                tags[t + receiver_len] == .period and
                tags[t + receiver_len + 1] == .identifier and
                tags[t + receiver_len + 2] == .l_paren and
                std.mem.eql(u8, tree.tokenSlice(t + receiver_len + 1), "pin"))
            {
                var same_receiver = true;
                var offset: Ast.TokenIndex = 0;
                while (offset < receiver_len) : (offset += 1) {
                    if (tags[t + offset] != tags[borrow.recv_first + offset] or
                        !std.mem.eql(u8, tree.tokenSlice(t + offset), tree.tokenSlice(borrow.recv_first + offset)))
                    {
                        same_receiver = false;
                        break;
                    }
                }
                if (same_receiver) return null;
            }
        }

        // Pattern A: `any_recv.gc_method(` — any receiver.
        if (tags[t] == .identifier and
            t + 3 <= last and
            tags[t + 1] == .period and
            tags[t + 2] == .identifier and
            tags[t + 3] == .l_paren)
        {
            const method = tree.tokenSlice(t + 2);
            if (isGcTriggerMethodName(method)) return t + 2;
        }

        // Pattern B: `callee_name(` — bare call (not method).
        // Skip if preceded by a period (mid-chain ident).
        if (tags[t] == .identifier and
            t + 1 <= last and
            tags[t + 1] == .l_paren and
            (t == 0 or tags[t - 1] != .period))
        {
            const callee_name = tree.tokenSlice(t);
            // Avoid matching Zig keywords that happen to be identifiers.
            if (!std.mem.eql(u8, callee_name, "true") and
                !std.mem.eql(u8, callee_name, "false") and
                !std.mem.eql(u8, callee_name, "null"))
            {
                if (calleeBodyMayInvokeGc(tree, cache, callee_name)) return t;
            }
        }

        // Pattern B': `try callee_name(` — peel try.
        if (tags[t] == .keyword_try and
            t + 2 <= last and
            tags[t + 1] == .identifier and
            tags[t + 2] == .l_paren)
        {
            const callee_name = tree.tokenSlice(t + 1);
            if (calleeBodyMayInvokeGc(tree, cache, callee_name)) return t + 1;
        }
    }
    return null;
}

fn reportProblem(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    b: SliceBorrow,
    gc_tok: Ast.TokenIndex,
) !void {
    const tags = tree.tokens.items(.tag);

    // Derive the callee display name for the message.
    const gc_callee: []const u8 = blk: {
        if (gc_tok >= 2 and
            tags[gc_tok - 1] == .period and
            tags[gc_tok - 2] == .identifier)
        {
            break :blk tree.tokenSlice(gc_tok);
        }
        break :blk tree.tokenSlice(gc_tok);
    };

    const starts = tree.tokens.items(.start);
    const receiver_path = tree.source[starts[b.recv_first] .. starts[b.recv_last] + tree.tokenSlice(b.recv_last).len];
    const msg = try std.fmt.allocPrint(
        gpa,
        "possible view from `{s}.{s}()` crosses `{s}(...)`; GC ownership and dispatch are unresolved — check the actual storage and callee lifetime contracts; if this is a GC-managed view, use the protection API its owner provides",
        .{ receiver_path, b.slice_method, gc_callee },
    );
    errdefer gpa.free(msg);

    const note_label = try std.fmt.allocPrint(
        gpa,
        "possible view produced here via `{s}.{s}()`",
        .{ receiver_path, b.slice_method },
    );
    errdefer gpa.free(note_label);

    const notes = try gpa.alloc(problem_mod.Note, 1);
    errdefer gpa.free(notes);
    notes[0] = .{
        .start = try Pos.fromTokenStart(tree, b.name_token),
        .end = try Pos.fromTokenEnd(tree, b.name_token),
        .label = note_label,
    };

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .warning,
        .start = try Pos.fromTokenStart(tree, gc_tok),
        .end = try Pos.fromTokenEnd(tree, gc_tok),
        .message = msg,
        .notes = notes,
    });
}

// ── Tests ────────────────────────────────────────────────────

test "arraybuffer-slice-without-pin: slice then direct GC method call fires" {
    try testing.expectFires(check, R,
        \\pub fn buggy(buf: anytype, vm: anytype) void {
        \\    const s = buf.slice();
        \\    _ = vm.call(s);
        \\}
        \\
    );
}

test "arraybuffer-slice-without-pin: utf8 then direct GC method call fires" {
    try testing.expectFires(check, R,
        \\pub fn buggy(buf: anytype, vm: anytype) void {
        \\    const s = buf.utf8();
        \\    _ = vm.evaluate(s);
        \\}
        \\
    );
}

test "arraybuffer-slice-without-pin: indirect call via same-file GC fn fires" {
    try testing.expectFires(check, R,
        \\pub fn gcTrigger(vm: anytype) void {
        \\    vm.call(null);
        \\}
        \\pub fn buggy(buf: anytype, vm: anytype) void {
        \\    const s = buf.slice();
        \\    gcTrigger(vm);
        \\    _ = s;
        \\}
        \\
    );
}

test "arraybuffer-slice-without-pin: pin on receiver between slice and GC call suppresses" {
    try testing.expectNoFire(check,
        \\pub fn ok(buf: anytype, vm: anytype, globalObject: anytype) void {
        \\    const s = buf.slice();
        \\    _ = buf.pin(globalObject);
        \\    _ = vm.call(s);
        \\}
        \\
    );
}

test "arraybuffer-slice-without-pin: no GC call does not fire" {
    try testing.expectNoFire(check,
        \\pub fn ok(buf: anytype) void {
        \\    const s = buf.slice();
        \\    _ = s;
        \\}
        \\
    );
}

test "arraybuffer-slice-without-pin: argv and path spellings remain an unknown advisory" {
    var problems = try testing.runRuleTyped(std.testing.allocator, check,
        \\const std = @import("std");
        \\pub fn main(init: std.process.Init) !void {
        \\    const args = try init.minimal.args.toSlice(init.arena.allocator());
        \\    const path = try std.fs.path.resolve(init.gpa, &.{ ".", "share" });
        \\    defer init.gpa.free(path);
        \\    _ = args.len;
        \\}
    );
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqual(problem_mod.Severity.warning, problems.items[0].severity);
    try std.testing.expectEqual(problem_mod.Verdict.unknown, problems.items[0].verdict);
}

test "arraybuffer-slice-without-pin: unknown nested buffer view still fires" {
    try testing.expectFires(check, R,
        \\pub fn use(holder: anytype, vm: anytype) void {
        \\    const bytes = holder.buffer.toSlice();
        \\    _ = vm.call(bytes);
        \\}
    );
}

test "arraybuffer-slice-without-pin: root pin does not protect nested buffer" {
    try testing.expectFires(check, R,
        \\pub fn use(holder: anytype, vm: anytype, globalObject: anytype) void {
        \\    const bytes = holder.buffer.toSlice();
        \\    _ = holder.pin(globalObject);
        \\    _ = vm.call(bytes);
        \\}
    );
}

test "arraybuffer-slice-without-pin: exact nested receiver pin suppresses" {
    try testing.expectNoFire(check,
        \\pub fn use(holder: anytype, vm: anytype, globalObject: anytype) void {
        \\    const bytes = holder.buffer.toSlice();
        \\    _ = holder.buffer.pin(globalObject);
        \\    _ = vm.call(bytes);
        \\}
    );
}
