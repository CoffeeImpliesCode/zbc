//! `<allocator>.destroy(<recv>.<field>);` / `<allocator>.free(<recv>.<field>);`
//! in a NON-destructor fn, without a subsequent `<recv>.<field> = null;`
//! (or `= &.{}`, `= .empty`).  The freed slot now holds a dangling
//! pointer.  Later reads via `if (<recv>.<field>) |h| use(h);` pass
//! the optional null-check (non-null) and `use(h)` is a UAF — or the
//! struct's own `deinit` re-frees the dangling slot for a double-free.
//!
//! Real-world: oven-sh/bun#30148 (`markInactive` freed handlers but
//! never set `.handlers = null`; later `if (handlers) |h|` passed and
//! crashed in `h.mode`), oven-sh/bun#30176, oven-sh/bun#29983,
//! oven-sh/bun#29988 — recurring "free without invalidate" shape in
//! mark-inactive / cancel / reset-style methods.
//!
//! Distinct from existing rules:
//!  - `heap-use-after-free` finds the USE site after a free; this
//!    rule fires at the FREE site so the bug is caught even before
//!    the use is written.
//!  - `free-then-try-realloc` is specifically about a fallible
//!    re-allocation that may leave the slot dangling on error.
//!  - `overwrite-without-deinit` is the dual: overwriting WITHOUT
//!    freeing the prior value.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip destructor-named fns (`deinit`, `destroy`, `finalize`,
//!      `dispose`, `free`, `close`) — leaving stale pointers in a
//!      struct that's about to be discarded is fine.
//!   2. Skip comptime type-builder fns.
//!   3. Walk the body for `<alloc>.destroy(<recv>.<field>);` or
//!      `<alloc>.free(<recv>.<field>);` where `<recv>` is a single
//!      identifier.
//!   4. After the free call's `;`, scan the remaining fn body for
//!      any assignment `<recv>.<field> = ...` or `<recv>.* = ...`
//!      at any depth.  If found, the field is reset → no fire.
//!   5. Otherwise fire at the free call site.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const skipDeferStmt = tokens.skipDeferStmt;
const matchParen = tokens.matchParen;
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipNestedFn = tokens.skipNestedFn;
const returnsType = tokens.returnsType;
const fnProto = tokens.fnProto;
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
    if (!config_mod.isEnabled(config, .free_without_null_then_check)) return;
    _ = cache;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const fp = fnProto(tree, &buf, node) orelse continue;
        const name_tok = fp.name_token orelse continue;
        if (isDestructorName(tree.tokenSlice(name_tok))) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, body, problems);
    }
}

/// Conservative allowlist of identifiers that look like an
/// allocator handle.  Used to filter out custom-receiver methods
/// like `link.free(self.page.?)` (where `link` is the destroyed
/// object and `self.page` is the allocator arg) from being treated
/// as `<alloc>.free(<recv>.<field>)`.  Matches by suffix /
/// substring patterns rather than an exact list to handle
/// project-specific allocator names like `string_alloc`,
/// `grapheme_alloc`, `default_allocator`, etc.
const isAllocatorishName = method_names.isAllocatorishName;

fn isDestructorName(name: []const u8) bool {
    // Prefix match: catches `deinit_slice`, `deinitInternal`,
    // `freeSlice`, `destroyOuter`, etc. — variants where the author
    // gave the destructor a more specific name.  Also `take*` /
    // `consume*` / `into*` methods which by convention consume the
    // receiver (the struct is intentionally invalid after the call).
    if (std.mem.startsWith(u8, name, "deinit") or
        std.mem.startsWith(u8, name, "destroy") or
        std.mem.startsWith(u8, name, "finalize") or
        std.mem.startsWith(u8, name, "dispose") or
        std.mem.startsWith(u8, name, "take") or
        std.mem.startsWith(u8, name, "consume") or
        std.mem.startsWith(u8, name, "into") or
        // Prefix match for `free*` catches `freeAndClear`, `freeAll`,
        // `freeBuffers`, etc.
        std.mem.startsWith(u8, name, "free") or
        std.mem.eql(u8, name, "close")) return true;
    // Substring match (capitalized): catches camelCase-prefixed
    // variants like `tempDeinit`, `partialDestroy`, `doCleanup`
    // where a qualifying prefix precedes the cleanup verb.
    return std.mem.indexOf(u8, name, "Deinit") != null or
        std.mem.indexOf(u8, name, "Destroy") != null or
        std.mem.indexOf(u8, name, "Cleanup") != null or
        std.mem.indexOf(u8, name, "Finalize") != null or
        std.mem.indexOf(u8, name, "Dispose") != null;
}

const Free = struct {
    recv_name: []const u8,
    field_name: []const u8,
    method_tok: Ast.TokenIndex,
    end_token: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var frees: std.ArrayListUnmanaged(Free) = .empty;
    defer frees.deinit(gpa);

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Skip `defer` / `errdefer` statements entirely — they're
        // deferred actions, not inline frees.  A `errdefer
        // allocator.destroy(self.scans);` registers cleanup for the
        // error path; not flagging the slot for reset is correct.
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = skipDeferStmt(tags, t, last) orelse last;
            continue;
        }
        // Pattern: `.<method>(<recv>.<field>...)` where method ∈
        // {destroy, free}.  `<method>` is preceded by `.` (so it's
        // a method call on something — could be a single allocator
        // var OR a chained `self.gpa.destroy(...)`).  The receiver
        // chain before `.<method>` must look like a real allocator
        // — we filter out custom-receiver methods (`link.free(x)`
        // where `link` is the freed object and `x` is the allocator
        // arg) by requiring the LHS of `.method` to be either a
        // single bare identifier (e.g., `gpa.destroy(...)`) OR a
        // `.<known-alloc-field>` chain (e.g., `self.gpa.destroy(...)`,
        // `bun.default_allocator.free(...)`).
        if (tags[t] != .identifier) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        const method = tree.tokenSlice(t);
        if (!std.mem.eql(u8, method, "destroy") and !std.mem.eql(u8, method, "free")) continue;
        // The token immediately before the `.` is the LHS of the
        // call chain.  If it's an identifier with allocator-ish
        // naming OR a known `default_allocator` style, accept.
        // Otherwise (e.g., `link` in `link.free(self.page.?)`)
        // skip — receiver is the freed thing, not an allocator.
        if (t < 2) continue;
        if (tags[t - 2] != .identifier) continue;
        const alloc_name = tree.tokenSlice(t - 2);
        if (!isAllocatorishName(alloc_name)) continue;
        if (tags[t + 1] != .l_paren) continue;
        const close = matchParen(tags, t + 1, last) orelse continue;
        // First 3 tokens after `(` must be `<recv> . <field>`.
        if (close <= t + 4) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        // After `<field>`, only these continuations name the slot
        // itself as the freed thing:
        //   - `)` — bare `<recv>.<field>`
        //   - `.?` (period + question_mark) — unwrap then free
        //   - `.*` (period + asterisk) — deref then free
        // Everything else (`(` method call, `[` slice/index,
        // `,` multi-arg) means the freed expression is a different
        // sub-expression and we'd be falsely flagging it.
        if (t + 5 > last) continue;
        const after = tags[t + 5];
        if (after == .r_paren) {
            // bare field — good
        } else if (after == .period and t + 6 <= last and
            (tags[t + 6] == .question_mark or tags[t + 6] == .asterisk))
        {
            // .? or .* — good
        } else continue;
        const recv = tree.tokenSlice(t + 2);
        const field = tree.tokenSlice(t + 4);
        // Restrict to canonical Zig method-receiver names.  This is
        // the rule's main precision lever — without it, hashmap
        // `entry.value_ptr`, result-struct `result.path`,
        // function-local container fields, and similar transient
        // borrows flood the report.  The Bun PR shapes all use
        // `self.X` / `this.X` — narrowing here drops the FP rate by
        // ~95% while preserving the canonical bug.
        if (!std.mem.eql(u8, recv, "self") and !std.mem.eql(u8, recv, "this")) continue;
        const sc = findStmtSemicolon(tags, close + 1, last) orelse continue;
        try frees.append(gpa, .{
            .recv_name = recv,
            .field_name = field,
            .method_tok = t,
            .end_token = sc,
        });
        t = sc;
    }

    for (frees.items) |f| {
        // Skip when the fn body also destroys the receiver itself —
        // `bun.destroy(this)` / `<alloc>.destroy(this)` / etc.  The
        // struct is going away; nulling its fields is pointless.
        // This is the common shape of non-`deinit`-named destructors
        // (`onClose`, `onResult`, `defer { ... bun.destroy(this); }`).
        if (fnDestroysReceiver(tree, first, last, f.recv_name)) continue;
        if (hasFieldReassign(tree, f.end_token + 1, last, f.recv_name, f.field_name)) continue;
        try report(gpa, problems, tree, f);
    }
}

/// True iff `[start, last]` contains a `destroy(<recv>)` call
/// (where `<recv>` matches the freed-field receiver).  Both
/// `<alloc>.destroy(<recv>)` and `bun.destroy(<recv>)` style.
fn fnDestroysReceiver(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "destroy")) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        if (tags[t + 1] != .l_paren) continue;
        // Single bare `<recv>` arg.
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .r_paren) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t + 2), recv)) return true;
    }
    return false;
}

/// True iff `[start, last]` contains an assignment that resets the
/// freed slot.  Three reset shapes are accepted:
///   - `<recv>.<field> = ...` (direct field assignment)
///   - `<recv>.* = ...` (whole-struct reset; e.g. `self.* = .{}`)
///   - `<recv> = ...` (whole-struct reassignment via pointer)
fn hasFieldReassign(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > last) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        // `<recv> = ...` — direct rebinding (rare for `self`).
        if (tags[t + 1] == .equal) return true;
        // `.*` is a single token, including in whole-struct resets.
        if (tags[t + 1] == .period_asterisk) {
            if (tags[t + 2] == .equal) return true;
            continue;
        }
        if (tags[t + 1] != .period) continue;
        if (t + 2 > last) continue;
        // `<recv>.<field> = ...` — direct field reset.
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field)) continue;
        if (t + 3 > last) continue;
        if (tags[t + 3] == .equal) return true;
        // `<recv>.<field>.<sub> = ...` — sub-field reset (e.g.
        // `this.buf.len = 0;` makes the slice empty by length even
        // though `.ptr` remains stale; widely-used pattern that
        // authors clearly intend as a "clear", so don't flag).
        if (tags[t + 3] == .period and t + 5 <= last and
            tags[t + 4] == .identifier and tags[t + 5] == .equal)
        {
            return true;
        }
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    f: Free,
) !void {
    const method = tree.tokenSlice(f.method_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "freed `{s}.{s}` via `.{s}()` but never reset the slot — `{s}.{s}` now holds a dangling pointer; a later `if ({s}.{s}) |h| use(h)` will pass the null-check (non-null) and UAF, or the struct's own `deinit` will double-free.  Add `{s}.{s} = null;` (or `= &.{{}};` / `= .empty;`) immediately after",
        .{ f.recv_name, f.field_name, method, f.recv_name, f.field_name, f.recv_name, f.field_name, f.recv_name, f.field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "free-without-null-then-check",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, f.method_tok),
        .end = try Pos.fromTokenEnd(tree, f.method_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "free-without-null-then-check: destroy then no reset fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    handlers: ?*Handlers,
        \\    const Handlers = struct {};
        \\    pub fn markInactive(self: *Self) void {
        \\        self.gpa.destroy(self.handlers.?);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("free-without-null-then-check", problems.items[0].rule_id);
}

test "free-without-null-then-check: destroy followed by null reset doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    handlers: ?*Handlers,
        \\    const Handlers = struct {};
        \\    pub fn markInactive(self: *Self) void {
        \\        self.gpa.destroy(self.handlers.?);
        \\        self.handlers = null;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free([]u8) then = &.{} doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    specifier: []const u8,
        \\    pub fn reset(self: *Self) void {
        \\        self.gpa.free(self.specifier);
        \\        self.specifier = &.{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: destructor fn (deinit) is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    handlers: ?*u8,
        \\    pub fn deinit(self: *Self) void {
        \\        self.gpa.destroy(self.handlers.?);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free(local) doesn't fire (only <recv>.<field>)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn foo(gpa: std.mem.Allocator) void {
        \\    const local = gpa.alloc(u8, 4) catch return;
        \\    gpa.free(local);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: sub-field reset (this.X.len = 0) doesn't fire" {
    // `this.X.len = 0;` makes the slice empty by length — `.ptr` is
    // still stale but no in-bounds access is possible, so authors
    // who write this clearly intend it as a "clear".  Accept.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    buf: []u8,
        \\    pub fn clearInput(self: *Self) void {
        \\        self.gpa.free(self.buf);
        \\        self.buf.len = 0;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: take* fn name is treated as consumer (skipped)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    pub fn takeLeftFreeRight(this: *Self, allocator: std.mem.Allocator) *u8 {
        \\        const ret: *u8 = undefined;
        \\        allocator.destroy(this.right);
        \\        return ret;
        \\    }
        \\    right: *u8,
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: non-allocator receiver doesn't fire" {
    // `link.free(self.page.?)` — `link` is the freed object (a
    // PageEntry); `self.page` is just the allocator arg.  The
    // receiver name `link` isn't allocator-ish, so skip.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Link = struct { pub fn free(_: *Link, _: usize) void {} };
        \\const Self = struct {
        \\    page: ?usize,
        \\    pub fn onDeleted(self: *const Self, link: *Link) void {
        \\        link.free(self.page.?);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free inside errdefer is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    scans: *u8,
        \\    pub fn init(self: *Self) !void {
        \\        self.scans = try self.gpa.create(u8);
        \\        errdefer self.gpa.destroy(self.scans);
        \\        _ = try doSomething();
        \\    }
        \\};
        \\fn doSomething() !void {}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: destructor-prefix fn names (deinit_slice) skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    buf: []u8,
        \\    pub fn deinit_slice(self: *Self, allocator: std.mem.Allocator) void {
        \\        allocator.free(self.buf);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: destructor of self (bun.destroy(this)) skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    url: []const u8,
        \\    pub fn onResult(this: *Self) void {
        \\        this.gpa.free(this.url);
        \\        bun.destroy(this);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: camelCase-prefixed destructor (tempDeinit) skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    gpa: std.mem.Allocator,
        \\    line_offsets: []u8,
        \\    pub fn tempDeinit(self: *Builder) void {
        \\        self.gpa.free(self.line_offsets);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: camelCase-prefixed destructor fires in non-cleanup fn" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    gpa: std.mem.Allocator,
        \\    line_offsets: []u8,
        \\    pub fn process(self: *Builder) void {
        \\        self.gpa.free(self.line_offsets);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: reassign to a fresh allocation counts as reset" {
    // Re-allocating into the same slot is a different bug (free-then-
    // try-realloc handles the fallible variant); here we just want to
    // verify a non-null reassignment suppresses the report.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    buf: []u8,
        \\    pub fn shrink(self: *Self) !void {
        \\        self.gpa.free(self.buf);
        \\        self.buf = try self.gpa.alloc(u8, 4);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: whole-receiver empty reset doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        self.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: whole-receiver undefined reset doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        self.* = undefined;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free without field or receiver reset fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: resetting another receiver still fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, other: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        other.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: whole-receiver read is not a reset" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        _ = self.*;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}
