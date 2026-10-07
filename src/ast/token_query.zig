//! Declarative token-pattern matcher.
//!
//! Rules describe SHAPES instead of writing bespoke token-walk
//! loops.  A Pattern is a sequence of Atoms; matching it against
//! a token position returns a Match (with captures) or null.
//!
//! Combine with scope-aware finders (findInSameScope /
//! findInEnclosingScope) to express the "bind X here, find use
//! of X later" pattern that nearly every rule needs.
//!
//! Example — `const X = try <openMethod>(...)` then later `X.close()`:
//!
//!     const open_call = comptime &[_]Atom{
//!         .{ .tok = .keyword_const },
//!         .{ .capture = 0 },              // X
//!         .{ .tok = .equal },
//!         .{ .opt = &[_]Atom{ .{ .tok = .keyword_try } } },
//!         .{ .tok = .identifier },        // receiver (e.g. dir)
//!         .{ .tok = .period },
//!         .{ .pred = isOpenerMethod },
//!         .paren_args,
//!     };
//!     const close_call = comptime &[_]Atom{
//!         .{ .ref = 0 },                  // X
//!         .{ .tok = .period },
//!         .{ .text = "close" },
//!         .paren_args,
//!     };
//!
//!     for (try findAll(gpa, tree, open_call, body_first, body_last)) |bind| {
//!         const close = findInSameScope(tree, close_call, bind.end + 1, body_last, &bind) orelse continue;
//!         // ...
//!     }

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("tokens.zig");

pub const TokenIndex = Ast.TokenIndex;
pub const TokenTag = tokens.TokenTag;

const MAX_CAPTURES: u8 = 8;
const MAX_RANGE_CAPTURES: u8 = 4;

/// Inclusive token range captured by `.capture_until`.  `end` >=
/// `start` when non-empty; the range CAN be empty (`start > end`)
/// if the stop tag was hit immediately.
pub const TokenRange = struct {
    start: TokenIndex,
    end: TokenIndex,

    pub fn isEmpty(self: TokenRange) bool {
        return self.start > self.end;
    }

    pub fn len(self: TokenRange) u32 {
        if (self.isEmpty()) return 0;
        return (self.end - self.start) + 1;
    }
};

/// One atomic match step.
pub const Atom = union(enum) {
    /// Consume one token whose tag equals this.  No text check.
    tok: TokenTag,
    /// Consume one identifier whose text equals this.
    text: []const u8,
    /// Consume one identifier whose text passes this predicate.
    pred: *const fn ([]const u8) bool,
    /// Consume one identifier whose text equals this AND record its
    /// position in captures[slot].  Use over `.text` when the matched
    /// token's position is needed at report time — avoids fragile
    /// `m.start + N` offsets.
    text_at: struct { slot: u8, text: []const u8 },
    /// Consume one identifier whose text passes this predicate AND
    /// record its position in captures[slot].  Use over `.pred` when
    /// the matched token's position is needed at report time.
    pred_at: struct { slot: u8, pred: *const fn ([]const u8) bool },
    /// Consume one identifier; record its position in captures[slot].
    capture: u8,
    /// Consume one identifier whose text equals tokenSlice(captures[slot]).
    ref: u8,
    /// Consume one .builtin token whose text equals this (e.g. "@memset").
    builtin: []const u8,
    /// Try to match the nested sequence; if any atom fails, rewind to
    /// before this opt and continue with the next atom.
    opt: []const Atom,
    /// Try each alternative in order; the first that matches wins.
    /// Each alternative is itself an atom sequence — useful for
    /// "pattern A OR pattern B at this position":
    ///     .{ .any_of = &[_][]const Atom{
    ///         &[_]Atom{ .{ .tok = .period_asterisk }, .{ .tok = .equal } },
    ///         &[_]Atom{ .{ .tok = .period }, .{ .tok = .identifier }, .{ .tok = .equal } },
    ///     }},
    /// If no alternative matches, the parent match fails (no rewind-
    /// and-continue like `.opt`).
    any_of: []const []const Atom,
    /// Consume a balanced `(...)`: opens with `(`, skips to matching
    /// `)`, advances past `)`.  Used for "ignore the call args".
    paren_args,
    /// Consume a balanced `[...]`.
    bracket_args,
    /// Consume a balanced `{...}`.
    brace_args,
    /// Consume tokens until (but NOT including) any of the `stops`
    /// tags at brace/paren/bracket depth 0 (relative to where the
    /// capture started).  Record the consumed range in
    /// range_captures[slot].  Used for `.free(<expr>)` style
    /// "capture this expression for later reference":
    ///     .{ .capture_until = .{ .slot = 0, .stops = &.{.r_paren} } }
    /// Empty captures (stop tag immediately) are allowed.
    capture_until: struct { slot: u8, stops: []const TokenTag },
    /// Match the previously-captured range token-by-token (both tag
    /// AND source-text must match for each token).  Advances past
    /// the matched range.  Fails on any mismatch or if slot empty.
    ref_range: u8,
};

/// Result of matching a Pattern at a position.
pub const Match = struct {
    /// First token of the match (the position passed to matchAt).
    start: TokenIndex,
    /// Last token of the match (inclusive).
    end: TokenIndex,
    /// captures[slot] is the token index of an identifier captured
    /// by `.capture = slot`; null if that slot wasn't filled.
    captures: [MAX_CAPTURES]?TokenIndex = @splat(null),
    /// range_captures[slot] is the token range captured by
    /// `.capture_until = .{ .slot = slot, ... }`; null if unfilled.
    range_captures: [MAX_RANGE_CAPTURES]?TokenRange = @splat(null),

    /// Convenience: text of capture slot N.
    pub fn captureText(self: Match, tree: *const Ast, slot: u8) ?[]const u8 {
        const tok = self.captures[slot] orelse return null;
        return tree.tokenSlice(tok);
    }
};

/// Try to match `atoms` starting at `pos`.  Returns a Match or null.
/// Captures from `inherited`, if non-null, are pre-loaded so `.ref`
/// atoms can reference previously-bound names.
pub fn matchAt(
    tree: *const Ast,
    atoms: []const Atom,
    pos: TokenIndex,
    last: TokenIndex,
    inherited: ?*const Match,
) ?Match {
    var m: Match = .{ .start = pos, .end = pos };
    if (inherited) |i| {
        m.captures = i.captures;
        m.range_captures = i.range_captures;
    }
    var t: TokenIndex = pos;
    if (matchSlice(tree, atoms, &t, last, &m.captures, &m.range_captures)) {
        if (t == pos) return null; // matched zero tokens — reject
        m.end = t - 1;
        return m;
    }
    return null;
}

/// Internal: try to match `atoms` against `t`, advancing `t` on
/// success and writing into `captures`.  Returns false on any atom
/// failure (t is left in an undefined state — caller doesn't reuse).
fn matchSlice(
    tree: *const Ast,
    atoms: []const Atom,
    t: *TokenIndex,
    last: TokenIndex,
    captures: *[MAX_CAPTURES]?TokenIndex,
    range_captures: *[MAX_RANGE_CAPTURES]?TokenRange,
) bool {
    const tags = tree.tokens.items(.tag);
    for (atoms) |a| {
        if (t.* > last) {
            // Allow opt to absorb end-of-range; other atoms fail.
            switch (a) {
                .opt => {}, // handled below — opt over end is a no-op
                else => return false,
            }
        }
        switch (a) {
            .tok => |want| {
                if (t.* > last or tags[t.*] != want) return false;
                t.* += 1;
            },
            .text => |want| {
                if (t.* > last or tags[t.*] != .identifier) return false;
                if (!std.mem.eql(u8, tree.tokenSlice(t.*), want)) return false;
                t.* += 1;
            },
            .pred => |p| {
                if (t.* > last or tags[t.*] != .identifier) return false;
                if (!p(tree.tokenSlice(t.*))) return false;
                t.* += 1;
            },
            .text_at => |ta| {
                if (ta.slot >= MAX_CAPTURES) return false;
                if (t.* > last or tags[t.*] != .identifier) return false;
                if (!std.mem.eql(u8, tree.tokenSlice(t.*), ta.text)) return false;
                captures[ta.slot] = t.*;
                t.* += 1;
            },
            .pred_at => |pa| {
                if (pa.slot >= MAX_CAPTURES) return false;
                if (t.* > last or tags[t.*] != .identifier) return false;
                if (!pa.pred(tree.tokenSlice(t.*))) return false;
                captures[pa.slot] = t.*;
                t.* += 1;
            },
            .capture => |slot| {
                if (slot >= MAX_CAPTURES) return false;
                if (t.* > last or tags[t.*] != .identifier) return false;
                captures[slot] = t.*;
                t.* += 1;
            },
            .ref => |slot| {
                if (slot >= MAX_CAPTURES) return false;
                const want_tok = captures[slot] orelse return false;
                if (t.* > last or tags[t.*] != .identifier) return false;
                if (!std.mem.eql(u8, tree.tokenSlice(t.*), tree.tokenSlice(want_tok))) return false;
                t.* += 1;
            },
            .builtin => |want| {
                if (t.* > last or tags[t.*] != .builtin) return false;
                if (!std.mem.eql(u8, tree.tokenSlice(t.*), want)) return false;
                t.* += 1;
            },
            .opt => |sub| {
                // Try to match nested; on failure, restore t and continue.
                const save = t.*;
                const save_caps = captures.*;
                const save_ranges = range_captures.*;
                if (!matchSlice(tree, sub, t, last, captures, range_captures)) {
                    t.* = save;
                    captures.* = save_caps;
                    range_captures.* = save_ranges;
                }
            },
            .any_of => |alts| {
                // First alternative that matches wins.  On all-fail the
                // parent match fails (unlike `.opt` which silently
                // continues with the next sibling atom).
                const save = t.*;
                const save_caps = captures.*;
                const save_ranges = range_captures.*;
                var matched = false;
                for (alts) |alt| {
                    if (matchSlice(tree, alt, t, last, captures, range_captures)) {
                        matched = true;
                        break;
                    }
                    t.* = save;
                    captures.* = save_caps;
                    range_captures.* = save_ranges;
                }
                if (!matched) return false;
            },
            .paren_args => {
                if (t.* > last or tags[t.*] != .l_paren) return false;
                const close = tokens.matchParen(tags, t.*, last) orelse return false;
                t.* = close + 1;
            },
            .bracket_args => {
                if (t.* > last or tags[t.*] != .l_bracket) return false;
                const close = tokens.matchBracket(tags, t.*, last) orelse return false;
                t.* = close + 1;
            },
            .brace_args => {
                if (t.* > last or tags[t.*] != .l_brace) return false;
                const close = tokens.matchBrace(tags, t.*, last) orelse return false;
                t.* = close + 1;
            },
            .capture_until => |cu| {
                if (cu.slot >= MAX_RANGE_CAPTURES) return false;
                const range_start = t.*;
                var depth: u32 = 0;
                var found = false;
                while (t.* <= last) : (t.* += 1) {
                    const tag = tags[t.*];
                    switch (tag) {
                        .l_paren, .l_brace, .l_bracket => depth += 1,
                        .r_paren, .r_brace, .r_bracket => {
                            if (depth > 0) {
                                depth -= 1;
                                continue;
                            }
                            // depth 0 closer — eligible stop
                        },
                        else => {},
                    }
                    if (depth == 0) {
                        for (cu.stops) |stop| {
                            if (tag == stop) {
                                found = true;
                                break;
                            }
                        }
                        if (found) break;
                    }
                }
                if (!found) return false;
                const range_end: TokenIndex = if (t.* == range_start) range_start else t.* - 1;
                range_captures[cu.slot] = .{
                    .start = range_start,
                    .end = range_end,
                };
                // Don't consume the stop token — caller's next atom does.
            },
            .ref_range => |slot| {
                if (slot >= MAX_RANGE_CAPTURES) return false;
                const range = range_captures[slot] orelse return false;
                if (range.isEmpty()) {
                    // Matches zero tokens — succeed without advancing.
                    continue;
                }
                const n = range.len();
                if (t.* + n - 1 > last) return false;
                var i: u32 = 0;
                while (i < n) : (i += 1) {
                    const cap_t: TokenIndex = range.start + i;
                    const cur_t: TokenIndex = t.* + i;
                    if (tags[cap_t] != tags[cur_t]) return false;
                    if (!std.mem.eql(u8, tree.tokenSlice(cap_t), tree.tokenSlice(cur_t))) return false;
                }
                t.* += n;
            },
        }
    }
    return true;
}

/// Find ALL non-overlapping matches of `atoms` in `[start, last]`.
/// After each match, scanning resumes at `match.end + 1`.  Does
/// NOT skip nested fns — pass a body range or use `findAllInBody`
/// when you need to confine to one fn's body.
pub fn findAll(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
) ![]Match {
    var out: std.ArrayListUnmanaged(Match) = .empty;
    var t: TokenIndex = start;
    while (t <= last) {
        if (matchAt(tree, atoms, t, last, null)) |m| {
            try out.append(gpa, m);
            t = m.end + 1;
            continue;
        }
        t += 1;
    }
    if (out.items.len == 0) return &.{};
    return out.toOwnedSlice(gpa);
}

/// Find ALL non-overlapping matches of `atoms` in `[start, last]`,
/// SKIPPING nested fn declarations entirely.  Use this when scanning
/// inside a fn body so that inner fn contents aren't double-matched.
/// Does NOT skip defer/errdefer statements — use
/// findAllInBodySkippingDefer if you want both.
pub fn findAllInBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
) ![]Match {
    var out: std.ArrayListUnmanaged(Match) = .empty;
    const tags = tree.tokens.items(.tag);
    var t: TokenIndex = start;
    while (t <= last) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            t = if (t < last) t + 1 else last + 1;
            continue;
        }
        if (matchAt(tree, atoms, t, last, null)) |m| {
            try out.append(gpa, m);
            t = m.end + 1;
            continue;
        }
        t += 1;
    }
    if (out.items.len == 0) return &.{};
    return out.toOwnedSlice(gpa);
}

/// Find ALL non-overlapping matches of `atoms` in `[start, last]`,
/// SKIPPING both nested fn declarations AND defer/errdefer
/// statements.  Use when matches inside deferred code shouldn't
/// count toward the rule (because they fire at a different point
/// in the fn's lifetime).
pub fn findAllInBodySkippingDefer(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
) ![]Match {
    var out: std.ArrayListUnmanaged(Match) = .empty;
    const tags = tree.tokens.items(.tag);
    var t: TokenIndex = start;
    while (t <= last) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            t = if (t < last) t + 1 else last + 1;
            continue;
        }
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            const end = tokens.skipDeferStmt(tags, t, last) orelse {
                t = last + 1;
                continue;
            };
            t = end + 1;
            continue;
        }
        if (matchAt(tree, atoms, t, last, null)) |m| {
            try out.append(gpa, m);
            t = m.end + 1;
            continue;
        }
        t += 1;
    }
    if (out.items.len == 0) return &.{};
    return out.toOwnedSlice(gpa);
}

/// Find FIRST match of `atoms` at the SAME LEXICAL BLOCK DEPTH as
/// `start`.  Skips nested `{...}` blocks entirely (their contents
/// are deeper-scope) and `defer`/`errdefer` statements (deferred,
/// not inline).  Stops at the enclosing scope's `}`.
///
/// `bound` (if non-null) provides captures that `.ref` atoms can
/// resolve against — for "find X.close() where X was the binding".
pub fn findInSameScope(
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
    bound: ?*const Match,
) ?Match {
    const tags = tree.tokens.items(.tag);
    if (start > last) return null;
    var t: TokenIndex = start;
    while (t <= last) {
        if (tags[t] == .l_brace) {
            t = (tokens.matchBrace(tags, t, last) orelse return null) + 1;
            continue;
        }
        if (tags[t] == .r_brace) return null;
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = (tokens.skipDeferStmt(tags, t, last) orelse return null) + 1;
            continue;
        }
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            t = if (t < last) t + 1 else last + 1;
            continue;
        }
        if (matchAt(tree, atoms, t, last, bound)) |m| return m;
        t += 1;
    }
    return null;
}

/// Find FIRST match of `atoms` within the ENCLOSING `{...}` scope
/// of `start`.  Allows nested blocks inside the scope (descends
/// into them).  Stops at the enclosing scope's `}`.
///
/// Use this for "find any USE of X anywhere in the rest of the
/// enclosing scope" — vs findInSameScope which restricts to same
/// block depth.
pub fn findInEnclosingScope(
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
    bound: ?*const Match,
) ?Match {
    const tags = tree.tokens.items(.tag);
    if (start > last) return null;
    var depth: i32 = 0;
    var t: TokenIndex = start;
    while (t <= last) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => {
                if (depth == 0) return null;
                depth -= 1;
            },
            else => {},
        }
        if (matchAt(tree, atoms, t, last, bound)) |m| return m;
        t += 1;
    }
    return null;
}

/// True iff `atoms` matches at position `start` AND consumes the
/// range exactly through `last`.  Useful for "is the RHS of this
/// binding EXACTLY this shape (no trailing chain)?"
pub fn matchExact(
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
    bound: ?*const Match,
) ?Match {
    if (start > last) return null;
    const m = matchAt(tree, atoms, start, last, bound) orelse return null;
    if (m.end != last) return null;
    return m;
}

/// True iff `atoms` matches anywhere in `[start, last]`, INCLUDING
/// inside defer/errdefer (which findInSameScope skips).  Used for
/// "is there ANY .release() in this fn body, even guarded by defer".
pub fn anyMatchAnywhere(
    tree: *const Ast,
    atoms: []const Atom,
    start: TokenIndex,
    last: TokenIndex,
    bound: ?*const Match,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > last) return false;
    var t: TokenIndex = start;
    while (t <= last) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            t = if (t < last) t + 1 else last + 1;
            continue;
        }
        if (matchAt(tree, atoms, t, last, bound)) |_| return true;
        t += 1;
    }
    return false;
}

// ── Tests ──────────────────────────────────────────────────

const testing = std.testing;

fn parseTokens(src: [:0]const u8) !Ast {
    return try Ast.parse(testing.allocator, src, .zig);
}

fn findIdent(tree: *const Ast, name: []const u8) TokenIndex {
    const tags = tree.tokens.items(.tag);
    var i: TokenIndex = 0;
    while (i < tree.tokens.len) : (i += 1) {
        if (tags[i] == .identifier and std.mem.eql(u8, tree.tokenSlice(i), name)) return i;
    }
    unreachable;
}

test "matchAt: simple tag sequence" {
    var tree = try parseTokens("fn f() void { const x = 1; }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const atoms = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .tok = .identifier },
        .{ .tok = .equal },
        .{ .tok = .number_literal },
    };
    const x_pos = findIdent(&tree, "x");
    const m = matchAt(&tree, atoms, x_pos - 1, last, null).?;
    try testing.expectEqual(@as(TokenIndex, x_pos - 1), m.start);
    try testing.expectEqual(@as(TokenIndex, x_pos + 2), m.end);
}

test "matchAt: capture and ref" {
    var tree = try parseTokens("fn f() void { const x = y; const z = x; }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    // Pattern: `const $0 = ...`
    const bind = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
    };
    const x_pos = findIdent(&tree, "x");
    const b = matchAt(&tree, bind, x_pos - 1, last, null).?;
    try testing.expectEqualStrings("x", b.captureText(&tree, 0).?);

    // Pattern: `$0` (ref) — find a use of x.
    const use = &[_]Atom{.{ .ref = 0 }};
    const use_m = findInEnclosingScope(&tree, use, b.end + 1, last, &b).?;
    try testing.expectEqualStrings("x", tree.tokenSlice(use_m.start));
}

test "matchAt: text_at captures the matched token" {
    var tree = try parseTokens("fn f() void { a.free(x); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const atoms = &[_]Atom{
        .{ .tok = .identifier },
        .{ .tok = .period },
        .{ .text_at = .{ .slot = 0, .text = "free" } },
        .paren_args,
    };
    const a_pos = findIdent(&tree, "a");
    const m = matchAt(&tree, atoms, a_pos, last, null).?;
    try testing.expectEqualStrings("free", m.captureText(&tree, 0).?);
}

test "matchAt: pred_at captures the matched token" {
    var tree = try parseTokens("fn f() void { a.openFile(); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const isOpener = struct {
        fn p(name: []const u8) bool {
            return std.mem.eql(u8, name, "openFile");
        }
    }.p;
    const atoms = &[_]Atom{
        .{ .tok = .identifier },
        .{ .tok = .period },
        .{ .pred_at = .{ .slot = 0, .pred = isOpener } },
        .paren_args,
    };
    const a_pos = findIdent(&tree, "a");
    const m = matchAt(&tree, atoms, a_pos, last, null).?;
    try testing.expectEqualStrings("openFile", m.captureText(&tree, 0).?);
}

test "matchAt: predicate" {
    var tree = try parseTokens("fn f() void { dir.openFile(); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const isOpener = struct {
        fn p(name: []const u8) bool {
            return std.mem.eql(u8, name, "openFile") or std.mem.eql(u8, name, "createFile");
        }
    }.p;
    const atoms = &[_]Atom{
        .{ .tok = .identifier },
        .{ .tok = .period },
        .{ .pred = isOpener },
        .paren_args,
    };
    const dir_pos = findIdent(&tree, "dir");
    const m = matchAt(&tree, atoms, dir_pos, last, null).?;
    try testing.expectEqual(@as(TokenIndex, dir_pos), m.start);
}

test "matchAt: capture_until + ref_range" {
    // Match `.free(<expr>);` followed (after closing brace skipping)
    // by `<same-expr> = try ...` — the canonical free_then_try_realloc shape.
    var tree = try parseTokens("fn f() void { x.free(s.cols); s.cols = try x.realloc(s.cols, 1); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);

    const free_pattern = &[_]Atom{
        .{ .tok = .identifier }, // receiver (x)
        .{ .tok = .period },
        .{ .text = "free" },
        .{ .tok = .l_paren },
        .{ .capture_until = .{ .slot = 0, .stops = &.{.r_paren} } },
        .{ .tok = .r_paren },
        .{ .tok = .semicolon },
    };
    const reassign_pattern = &[_]Atom{
        .{ .ref_range = 0 },
        .{ .tok = .equal },
        .{ .tok = .keyword_try },
    };

    const free_matches = try findAll(testing.allocator, &tree, free_pattern, 0, last);
    defer testing.allocator.free(free_matches);
    try testing.expectEqual(@as(usize, 1), free_matches.len);

    // Now look for the reassignment immediately after the `;` of the free.
    const after_free = free_matches[0].end + 1;
    const reassign = matchAt(&tree, reassign_pattern, after_free, last, &free_matches[0]);
    try testing.expect(reassign != null);
}

test "matchAt: ref_range mismatch fails" {
    var tree = try parseTokens("fn f() void { x.free(a.b); c.d = try x.alloc(); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);

    const free_pattern = &[_]Atom{
        .{ .tok = .identifier },
        .{ .tok = .period },
        .{ .text = "free" },
        .{ .tok = .l_paren },
        .{ .capture_until = .{ .slot = 0, .stops = &.{.r_paren} } },
        .{ .tok = .r_paren },
        .{ .tok = .semicolon },
    };
    const reassign_pattern = &[_]Atom{
        .{ .ref_range = 0 },
        .{ .tok = .equal },
    };
    const fm = (try findAll(testing.allocator, &tree, free_pattern, 0, last))[0..];
    defer testing.allocator.free(fm);
    // Captured `a.b` but next stmt is `c.d = ...` — ref_range should fail.
    const r = matchAt(&tree, reassign_pattern, fm[0].end + 1, last, &fm[0]);
    try testing.expect(r == null);
}

test "matchAt: any_of picks the first matching alternative" {
    var tree = try parseTokens("fn f() void { x.* = 1; y.field = 2; z = 3; }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    // Pattern: `<id> (.* = | . <id> =) ...` — capture the LHS.
    const atoms = &[_]Atom{
        .{ .capture = 0 },
        .{ .any_of = &[_][]const Atom{
            &[_]Atom{ .{ .tok = .period_asterisk }, .{ .tok = .equal } },
            &[_]Atom{ .{ .tok = .period }, .{ .tok = .identifier }, .{ .tok = .equal } },
        } },
    };
    const matches = try findAll(testing.allocator, &tree, atoms, 0, last);
    defer testing.allocator.free(matches);
    // Should match `x.* =` and `y.field =` but NOT bare `z = 3` (no
    // alternative covers a bare `=` after the identifier).
    try testing.expectEqual(@as(usize, 2), matches.len);
    try testing.expectEqualStrings("x", matches[0].captureText(&tree, 0).?);
    try testing.expectEqualStrings("y", matches[1].captureText(&tree, 0).?);
}

test "matchAt: any_of fails if no alternative matches" {
    var tree = try parseTokens("fn f() void { x = 1; }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const atoms = &[_]Atom{
        .{ .capture = 0 },
        .{ .any_of = &[_][]const Atom{
            &[_]Atom{.{ .tok = .period_asterisk }},
            &[_]Atom{.{ .tok = .period }},
        } },
    };
    const matches = try findAll(testing.allocator, &tree, atoms, 0, last);
    defer testing.allocator.free(matches);
    try testing.expectEqual(@as(usize, 0), matches.len);
}

test "matchAt: opt" {
    var tree = try parseTokens("fn f() void { const x = try foo(); const y = bar(); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    // Pattern: `const $0 = [try] <ident>()`
    const atoms = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
        .{ .opt = &[_]Atom{.{ .tok = .keyword_try }} },
        .{ .tok = .identifier },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, atoms, 0, last);
    defer testing.allocator.free(matches);
    try testing.expectEqual(@as(usize, 2), matches.len);
    try testing.expectEqualStrings("x", matches[0].captureText(&tree, 0).?);
    try testing.expectEqualStrings("y", matches[1].captureText(&tree, 0).?);
}

test "matchAt: builtin" {
    var tree = try parseTokens("fn f() void { @memset(buf, 0); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const atoms = &[_]Atom{
        .{ .builtin = "@memset" },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, atoms, 0, last);
    defer testing.allocator.free(matches);
    try testing.expectEqual(@as(usize, 1), matches.len);
}

test "matchAt: paren_args skips balanced parens" {
    var tree = try parseTokens("fn f() void { foo(bar(1, 2), 3); }");
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const atoms = &[_]Atom{
        .{ .text = "foo" },
        .paren_args,
        .{ .tok = .semicolon },
    };
    const matches = try findAll(testing.allocator, &tree, atoms, 0, last);
    defer testing.allocator.free(matches);
    try testing.expectEqual(@as(usize, 1), matches.len);
}

test "findInSameScope: skips nested blocks" {
    var tree = try parseTokens(
        \\fn f() void {
        \\    const x = open();
        \\    { x.close(); }
        \\}
    );
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const bind = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
        .{ .text = "open" },
        .paren_args,
    };
    const close = &[_]Atom{
        .{ .ref = 0 },
        .{ .tok = .period },
        .{ .text = "close" },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, bind, 0, last);
    defer testing.allocator.free(matches);
    const b = matches[0];
    // The close is in a nested block — same-scope find should miss it.
    const found = findInSameScope(&tree, close, b.end + 1, last, &b);
    try testing.expect(found == null);
}

test "findInSameScope: skips defer" {
    var tree = try parseTokens(
        \\fn f() void {
        \\    const x = open();
        \\    defer x.close();
        \\}
    );
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const bind = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
        .{ .text = "open" },
        .paren_args,
    };
    const close = &[_]Atom{
        .{ .ref = 0 },
        .{ .tok = .period },
        .{ .text = "close" },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, bind, 0, last);
    defer testing.allocator.free(matches);
    const b = matches[0];
    const found = findInSameScope(&tree, close, b.end + 1, last, &b);
    try testing.expect(found == null);
}

test "findInSameScope: inline close hits" {
    var tree = try parseTokens(
        \\fn f() void {
        \\    const x = open();
        \\    x.close();
        \\}
    );
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const bind = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
        .{ .text = "open" },
        .paren_args,
    };
    const close = &[_]Atom{
        .{ .ref = 0 },
        .{ .tok = .period },
        .{ .text = "close" },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, bind, 0, last);
    defer testing.allocator.free(matches);
    const b = matches[0];
    const found = findInSameScope(&tree, close, b.end + 1, last, &b);
    try testing.expect(found != null);
}

test "findInEnclosingScope: descends into nested blocks" {
    var tree = try parseTokens(
        \\fn f() void {
        \\    const x = open();
        \\    { _ = x; }
        \\}
    );
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const bind = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
        .{ .text = "open" },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, bind, 0, last);
    defer testing.allocator.free(matches);
    const b = matches[0];
    const use = &[_]Atom{.{ .ref = 0 }};
    const found = findInEnclosingScope(&tree, use, b.end + 1, last, &b);
    try testing.expect(found != null);
}

test "findInEnclosingScope: stops at scope close" {
    var tree = try parseTokens(
        \\fn f() void {
        \\    { const x = open(); }
        \\    _ = x;
        \\}
    );
    defer tree.deinit(testing.allocator);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    const bind = &[_]Atom{
        .{ .tok = .keyword_const },
        .{ .capture = 0 },
        .{ .tok = .equal },
        .{ .text = "open" },
        .paren_args,
    };
    const matches = try findAll(testing.allocator, &tree, bind, 0, last);
    defer testing.allocator.free(matches);
    const b = matches[0];
    const use = &[_]Atom{.{ .ref = 0 }};
    const found = findInEnclosingScope(&tree, use, b.end + 1, last, &b);
    // The use of `x` in the sibling scope shouldn't be reachable
    // from inside the brace block where x was bound.
    try testing.expect(found == null);
}
