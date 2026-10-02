//! Detects struct literal field copies of the form `.field = recv.field`
//! where the field name suggests a refcounted or owned type and no
//! ref-acquire method (clone/dupeRef/ref/retain/…) is called on the
//! source in the nearby tokens.
//!
//! Real-world shapes:
//!   oven-sh/bun#30955 — `Blob.name` bitwise-copied without calling
//!   `.dupeRef()`; both the source and the copy call `name.deinit()` →
//!   double-decrement → SIGFPE.
//!   oven-sh/bun#30991 — WTF string ref copied without `ref()`.
//!   oven-sh/bun#30882 — specifier field copied without `dupe_ref()`.
//!
//! Detection (purely syntactic, two-pass per-file token walk):
//!
//!   Pass 1 — evidence collection:
//!     Scan the entire file for calls of the form:
//!       `receiver . field_name . <acquire_or_release_method> (`
//!     where acquire methods: clone/dupeRef/ref/retain/dupe/addRef
//!           release methods: deinit/deref/free/release/unref/destroy/drop
//!     For each such `field_name`, record it as "evidenced" — this file
//!     treats that field as a refcounted or managed type.
//!
//!   Pass 2 — copy check (per fn body):
//!     Scan for the struct literal field-init pattern:
//!       t+0: `.period`
//!       t+1: `.identifier`  (dest_field)
//!       t+2: `.equal`
//!       t+3: `.identifier`  (source_recv)
//!       t+4: `.period`
//!       t+5: `.identifier`  (source_field, same text as dest_field)
//!     AND `dest_field == source_field`.
//!     The field name must match the refcounted-substring list.
//!     The field name must be in the "evidenced" set from Pass 1.
//!     In the window [t-10, t) there must be no acquire call on source.
//!     Fire at t+1.
//!
//!   Evidence requirement eliminates value-type false positives:
//!     `Ref = packed struct(u64)` (bun's symbol-table index) has no
//!     `.ref()`, `.clone()`, `.deinit()` etc. — it is never evidenced.
//!     WTF::String (`name`, `str`) has `.dupeRef()` and `.deinit()` call
//!     sites in the same file — it is evidenced and correctly fires.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");

const skipFnDecl = tokens.skipFnDecl;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ref-counted-copy-without-dupe";

/// Field name substrings that suggest the field holds a refcounted
/// or heap-owned value.
const refcounted_substrings = [_][]const u8{
    "name", "str", "string", "ref", "handle", "buf", "data", "content",
};

/// State threaded through the two-pass check.
const CheckState = struct {
    problems: *std.ArrayListUnmanaged(Problem),
    /// Field names for which at least one acquire OR release call was found
    /// in the file.  Only these field names are eligible for copy-checking.
    evidenced: *const std.StringHashMap(void),
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ref_counted_copy_without_dupe)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    // ── Pass 1: collect evidenced field names ─────────────────────────────
    // Scan the whole file for `identifier . FIELD . <acquire_or_release> (`.
    // A field that is never acquire-called OR release-called has no lifecycle
    // management — it is a plain value type and should not be flagged.
    var evidenced = std.StringHashMap(void).init(gpa);
    defer evidenced.deinit();

    if (last_tok >= 5) {
        var t: Ast.TokenIndex = 0;
        while (t + 5 <= last_tok) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (tags[t + 3] != .period) continue;
            if (tags[t + 4] != .identifier) continue;
            if (tags[t + 5] != .l_paren) continue;
            const field = tree.tokenSlice(t + 2);
            if (!isRefcountedFieldName(field)) continue;
            const method = tree.tokenSlice(t + 4);
            if (method_names.isRefAcquireName(method) or isRefReleaseName(method)) {
                try evidenced.put(field, {});
            }
        }
    }

    // If no evidenced fields exist in this file, nothing to flag.
    if (evidenced.count() == 0) return;

    // ── Pass 2: check for copies without acquire ──────────────────────────
    var state = CheckState{ .problems = problems, .evidenced = &evidenced };
    try tokens.forEachFnBody(gpa, tree, &state, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    state: *CheckState,
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }

        // Pattern: `. dest_field = source_recv . source_field`
        //   t+0: period
        //   t+1: identifier  (dest_field)
        //   t+2: equal
        //   t+3: identifier  (source_recv)
        //   t+4: period
        //   t+5: identifier  (source_field)
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .identifier) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier) continue;

        const dest_field = tree.tokenSlice(t + 1);
        const source_recv = tree.tokenSlice(t + 3);
        const source_field = tree.tokenSlice(t + 5);

        // Both sides must name the same field.
        if (!std.mem.eql(u8, dest_field, source_field)) continue;

        // Field name must suggest a refcounted / owned type.
        if (!isRefcountedFieldName(dest_field)) continue;

        // Evidence gate: only fire when this file contains at least one
        // acquire or release call for this field name.  Value types (e.g.
        // `Ref = packed struct(u64)`) never appear with `.ref.deinit()` or
        // `.ref.clone()` — they have no lifecycle methods.
        if (!state.evidenced.contains(dest_field)) continue;

        // Suppress when the RHS is not a bare `source_recv.source_field` but has
        // any further access — a method call (`recv.field.method(…)`) or sub-field
        // (`recv.field.subfield`).  In both cases the value assigned is derived
        // rather than a raw refcount-unsafe copy.
        //   t+4: period, t+5: source_field, t+6: period  ← any further access
        if (t + 6 <= last and tags[t + 6] == .period) continue;

        // Also check that no ref-acquire is called on source_recv.source_field
        // in the 10 tokens preceding t (backward-scan for manual pre-clone).
        const window_start = t -| 10;
        if (hasRefAcquireCall(tree, tags, window_start, t -| 1, source_recv, source_field)) continue;

        // Suppress the MOVE pattern: if within the next 100 tokens the SOURCE
        // is reset to empty (`source_recv.source_field = {}` or `.{}`), the
        // assignment is an ownership transfer, not a shared-ref copy.  A move
        // does not increase the refcount — the receiver acquires the single
        // existing ref and the source is disarmed.
        if (sourceIsClearedAfter(tree, tags, t + 6, @min(t + 100, last), source_recv, source_field))
            continue;

        try report(gpa, state.problems, tree, t + 1, dest_field, source_recv);
    }
}

/// True iff within `[start, end]` the SOURCE is reset to an empty value
/// (`source_recv . source_field = { }` or `= .{ }` or `= .empty`).  This
/// pattern signals an ownership MOVE — the field is transferred from the
/// source to the destination, then zeroed.  A move does not increment the
/// refcount; both sides share the original (sole) reference, and the source
/// being cleared prevents any double-release.
fn sourceIsClearedAfter(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    source_recv: []const u8,
    source_field: []const u8,
) bool {
    if (start + 4 > end) return false;
    var k = start;
    while (k + 4 <= end) : (k += 1) {
        // Pattern: identifier(source_recv) . identifier(source_field) = { }
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), source_recv)) continue;
        if (k + 1 > end or tags[k + 1] != .period) continue;
        if (k + 2 > end or tags[k + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k + 2), source_field)) continue;
        if (k + 3 > end or tags[k + 3] != .equal) continue;
        // Empty init: `= {}`, `= .{}`, or `.empty`
        if (k + 4 > end) continue;
        switch (tags[k + 4]) {
            .l_brace => return true, // `= {`
            .period => {
                if (k + 5 > end) continue;
                switch (tags[k + 5]) {
                    .l_brace => return true, // `= .{`
                    .identifier => { // `= .empty` / `= .none` / `= .zero`
                        const w = tree.tokenSlice(k + 5);
                        if (std.mem.eql(u8, w, "empty") or
                            std.mem.eql(u8, w, "none") or
                            std.mem.eql(u8, w, "zero") or
                            std.mem.eql(u8, w, "init")) return true;
                    },
                    else => {},
                }
            },
            else => {},
        }
    }
    return false;
}

/// True iff `name` is a method that RELEASES or deallocates a refcounted value.
/// Used (alongside isRefAcquireName) to detect field lifecycle evidence.
fn isRefReleaseName(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "deref") or
        std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "unref") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "drop");
}

/// True iff any underscore-delimited word component of `name` exactly matches
/// one of the refcounted substrings.  Whole-word matching prevents short
/// substrings like "ref" from firing on compound names like "react_fast_refresh",
/// or "name" from firing on "rename".
///
/// Also suppressed when the last component is all-digits (e.g. `user_data_64`,
/// `user_data_32`) — a numeric suffix strongly implies an integer type.
fn isRefcountedFieldName(name: []const u8) bool {
    // If the final underscore-component is purely numeric, the field almost
    // certainly holds an integer, not a refcounted pointer.
    if (std.mem.lastIndexOfScalar(u8, name, '_')) |last_us| {
        const suffix = name[last_us + 1 ..];
        if (suffix.len > 0) {
            var all_digits = true;
            for (suffix) |c| {
                if (!std.ascii.isDigit(c)) {
                    all_digits = false;
                    break;
                }
            }
            if (all_digits) return false;
        }
    }
    var it = std.mem.splitScalar(u8, name, '_');
    while (it.next()) |word| {
        for (refcounted_substrings) |sub| {
            if (std.mem.eql(u8, word, sub)) return true;
        }
    }
    return false;
}

/// True iff the token range [start, end] contains:
///   `source_recv . source_field . <acquire_method> (`
fn hasRefAcquireCall(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    source_recv: []const u8,
    source_field: []const u8,
) bool {
    if (start > end) return false;
    // Need at least 5 tokens: recv . field . method (
    if (end < start + 4) return false;
    var t: Ast.TokenIndex = start;
    while (t + 4 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), source_recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), source_field)) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        const method = tree.tokenSlice(t + 4);
        if (method_names.isRefAcquireName(method)) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    field_tok: Ast.TokenIndex,
    field: []const u8,
    recv: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "field `.{s}` is copied from `{s}.{s}` without calling `clone()`/`dupeRef()`/`ref()` — if `{s}` is refcounted, both the source and the copy will decrement the refcount on cleanup, potentially causing a double-free or SIGFPE; call `{s}.{s}.clone()` or the appropriate ref-acquire method",
        .{ field, recv, field, field, recv, field },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, field_tok),
        .end = Pos.fromTokenEnd(tree, field_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "ref-counted-copy-without-dupe: .name = other.name fires (with lifecycle evidence)" {
    try testing.expectFires(check, R,
        \\fn cleanup(s: anytype) void { s.name.deinit(); }
        \\fn copy(source: anytype) void {
        \\    const result = .{
        \\        .name = source.name,
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .handle = other.handle fires (with lifecycle evidence)" {
    try testing.expectFires(check, R,
        \\fn release(h: anytype) void { h.handle.release(); }
        \\fn copy(other: anytype) void {
        \\    const result = .{
        \\        .handle = other.handle,
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .name = source.name.clone() does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(s: anytype) void { s.name.deinit(); }
        \\fn copy(source: anytype) void {
        \\    const result = .{
        \\        .name = source.name.clone(),
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .count = other.count does not fire" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{
        \\        .count = other.count,
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .id = other.id does not fire" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{
        \\        .id = other.id,
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .str = other.str fires (with lifecycle evidence)" {
    try testing.expectFires(check, R,
        \\fn dealloc(other: anytype) void { other.str.deref(); }
        \\fn copy(other: anytype) void {
        \\    const result = .{
        \\        .str = other.str,
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .name = source.name.dupeRef() does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(s: anytype) void { s.name.deinit(); }
        \\fn copy(source: anytype) void {
        \\    const result = .{
        \\        .name = source.name.dupeRef(),
        \\    };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .rename = other.rename does not fire (whole-word)" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{ .rename = other.rename };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .metadata = other.metadata does not fire (whole-word)" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{ .metadata = other.metadata };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .react_fast_refresh = other.react_fast_refresh does not fire" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{ .react_fast_refresh = other.react_fast_refresh };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .user_data = other.user_data fires (data, with lifecycle)" {
    try testing.expectFires(check, R,
        \\fn release(other: anytype) void { other.user_data.deinit(); }
        \\fn copy(other: anytype) void {
        \\    const result = .{ .user_data = other.user_data };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .user_data_64 = other.user_data_64 does not fire (numeric suffix)" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{ .user_data_64 = other.user_data_64 };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .user_data_128 = other.user_data_128 does not fire (numeric suffix)" {
    try testing.expectNoFire(check,
        \\fn copy(other: anytype) void {
        \\    const result = .{ .user_data_128 = other.user_data_128 };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .name = other.name fires when deinit call exists in file" {
    try testing.expectFires(check, R,
        \\fn cleanup(s: anytype) void { s.name.deinit(); }
        \\fn copy(source: anytype) void {
        \\    const result = .{ .name = source.name };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .name = other.name does not fire without any lifecycle call" {
    try testing.expectNoFire(check,
        \\fn copy(source: anytype) void {
        \\    const result = .{ .name = source.name };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .ref = other.ref does not fire (no lifecycle — value type)" {
    try testing.expectNoFire(check,
        \\fn copy(st: anytype) void {
        \\    const result = .{ .ref = st.ref };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: .ref = other.ref fires when ref() call exists" {
    try testing.expectFires(check, R,
        \\fn acquire(s: anytype) void { _ = s.ref.ref(); }
        \\fn copy(st: anytype) void {
        \\    const result = .{ .ref = st.ref };
        \\    _ = result;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: move pattern (source cleared after) does not fire" {
    // `.ref = this.ref` followed by `this.ref = {}` is an OWNERSHIP TRANSFER
    // (move), not a shared-copy.  The source is zeroed out so there is only
    // ever one live reference at a time — no double-free.
    try testing.expectNoFire(check,
        \\fn acquire(s: anytype) void { _ = s.ref.ref(); }
        \\fn move(this: *Self) void {
        \\    const result = .{ .ref = this.ref };
        \\    this.ref = {};
        \\    _ = result;
        \\}
        \\
    );
}
