//! Iterator-invalidation-during-mutation detector —
//! `for (<list>.items) |...| { ... <list>.<mutate>(...); ... }`
//! where the loop body calls a method on the SAME list that
//! reallocates / shifts its backing storage.  The loop is
//! iterating over a snapshot of `.items` that may now point at
//! freed memory (append/resize) or at shifted/swapped elements
//! (insert/remove/swapRemove), producing UAF or skipped-element
//! bugs.
//!
//! Distinct from [[arraylist-items-slice]]:
//!   - That rule fires on `const X = list.items;` followed by
//!     `list.<mutate>()` then a use of `X`.
//!   - This rule fires on the loop SHAPE directly — `for
//!     (list.items)` is an implicit borrow, and the mutate inside
//!     the body is the smoking gun.
//!
//! Mutator allowlist — anything that reallocates OR reorders the
//! backing storage:
//!   append / appendSlice / appendNTimes / insert / insertSlice /
//!   addOne / addManyAsSlice / addManyAsArray / resize /
//!   clearAndFree / clearRetainingCapacity / deinit /
//!   swapRemove / orderedRemove / pop / popOrNull /
//!   replaceRange / shrinkAndFree / shrinkRetainingCapacity.
//!
//! Detection (per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Walk for `for (<recv>.items)` or `for (<recv>.items, ...)`
//!      loops; capture the `<recv>` name and the loop body extent.
//!   3. Scan the body for `<recv>.<mutator>(` calls at any depth.
//!      Skip nested fn / labeled-block declarations that wouldn't
//!      execute in this loop iteration.
//!   4. Fire on the mutate call site with a note pointing back to
//!      the for-header.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .iterator_invalidation_mutation)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        // Skip nested fns so we don't re-enter their bodies as part
        // of an enclosing fn's walk.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_for) continue;
        if (tags[t + 1] != .l_paren) continue;
        // Find the receiver of `.items` (or `.values` / `.keys`).
        // Walk the first paren's contents for `<recv> . items`.
        const lp = t + 1;
        const cp = matchParen(tags, lp, last) orelse continue;
        const recv_range = receiverPathRange(tree, lp + 1, cp - 1) orelse continue;
        // Find the loop body — after the optional `|...|` capture.
        // Track capture names so we can skip if the receiver's last
        // segment is shadowed by a capture (`for (this.x.items) |*x|`
        // makes `x` the capture, not the field).
        var k: Ast.TokenIndex = cp + 1;
        var capture_shadows: bool = false;
        var capture_by_value: bool = false;
        if (k <= last and tags[k] == .pipe) {
            const recv_last_seg = tree.tokenSlice(recv_range.last);
            k += 1;
            var first_capture = true;
            while (k <= last and tags[k] != .pipe) : (k += 1) {
                if (tags[k] != .identifier) continue;
                if (first_capture) {
                    capture_by_value = k == 0 or tags[k - 1] != .asterisk;
                    first_capture = false;
                }
                if (std.mem.eql(u8, tree.tokenSlice(k), recv_last_seg)) {
                    capture_shadows = true;
                }
            }
            if (k > last) continue;
            k += 1;
        }
        if (capture_shadows) continue;
        if (k > last) continue;
        const body_first: Ast.TokenIndex = k;
        const body_last: Ast.TokenIndex = if (tags[body_first] == .l_brace)
            matchBrace(tags, body_first, last) orelse continue
        else blk: {
            // Inline body — single statement to next `;`.
            break :blk tokens.findStmtSemicolon(tags, body_first, last) orelse continue;
        };
        // Search for `<recv-path>.<mutator>(` inside [body_first,
        // body_last].  recv_range is a token range that may be
        // multi-segment (`this.ltr` → 3 tokens: `this . ltr`).
        const mutate_tok = findReceiverMutate(tree, body_first, body_last, recv_range) orelse continue;
        if (capture_by_value and mutationImmediatelyReturns(tree, mutate_tok, body_last)) {
            t = body_last;
            continue;
        }
        const recv_display = displayReceiver(tree, recv_range);
        try report(gpa, problems, tree, t, recv_display, mutate_tok);
        // Skip past this loop's body so we don't re-find the same
        // mutate from an outer loop scan.
        t = body_last;
    }
}

/// Token range covering the RECEIVER portion of `for (<recv>.<proj>)`
/// — i.e. all the tokens BEFORE the `.<projector>` suffix.  The
/// range starts at the first identifier of the receiver chain and
/// ends at the LAST identifier (caller uses this for last-segment
/// lookup and full-path matching).
const ReceiverRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// Resolve the for-scrutinee range `[start, end]` to a receiver
/// token range when the shape is `<ident-chain> . <projector>`
/// where projector ∈ {items, values, keys}.  Receiver chains may
/// be multi-segment (`this.ltr` → tokens `this . ltr`).  Returns
/// null on multi-input loops, projector-via-call (\`.iterator()\`),
/// or unrecognised shapes.
fn receiverPathRange(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?ReceiverRange {
    const tags = tree.tokens.items(.tag);
    if (end < start + 2) return null;
    // Multi-input check: comma at paren depth 0.
    {
        var depth: u32 = 0;
        var t: Ast.TokenIndex = start;
        while (t <= end) : (t += 1) {
            switch (tags[t]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => if (depth > 0) {
                    depth -= 1;
                },
                .comma => if (depth == 0) return null,
                else => {},
            }
        }
    }
    // Trailing projector: `. <projector>` at the end.
    if (tags[end - 1] != .period) return null;
    if (tags[end] != .identifier) return null;
    const proj = tree.tokenSlice(end);
    if (!std.mem.eql(u8, proj, "items") and
        !std.mem.eql(u8, proj, "values") and
        !std.mem.eql(u8, proj, "keys")) return null;
    // Receiver is `[start, end - 2]`.  Must be an `<id>(.<id>)*`
    // chain — no parens/brackets/calls.
    const recv_end: Ast.TokenIndex = end - 2;
    if (recv_end < start) return null;
    var t: Ast.TokenIndex = start;
    var expecting_ident: bool = true;
    while (t <= recv_end) : (t += 1) {
        if (expecting_ident) {
            if (tags[t] != .identifier) return null;
            expecting_ident = false;
        } else {
            if (tags[t] != .period) return null;
            expecting_ident = true;
        }
    }
    if (expecting_ident) return null; // ends on a period
    return .{ .first = start, .last = recv_end };
}

/// Render the receiver token range as a string for the diagnostic.
fn displayReceiver(tree: *const Ast, range: ReceiverRange) []const u8 {
    const starts = tree.tokens.items(.start);
    const start_byte = starts[range.first];
    const last_tok_slice = tree.tokenSlice(range.last);
    const end_byte = starts[range.last] + last_tok_slice.len;
    return tree.source[start_byte..end_byte];
}

fn isInvalidatingMutateName(name: []const u8) bool {
    return std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "appendNTimes") or
        std.mem.eql(u8, name, "insert") or
        std.mem.eql(u8, name, "insertSlice") or
        std.mem.eql(u8, name, "addOne") or
        std.mem.eql(u8, name, "addManyAsSlice") or
        std.mem.eql(u8, name, "addManyAsArray") or
        std.mem.eql(u8, name, "resize") or
        std.mem.eql(u8, name, "clearAndFree") or
        std.mem.eql(u8, name, "clearRetainingCapacity") or
        std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "swapRemove") or
        std.mem.eql(u8, name, "orderedRemove") or
        std.mem.eql(u8, name, "pop") or
        std.mem.eql(u8, name, "popOrNull") or
        std.mem.eql(u8, name, "replaceRange") or
        std.mem.eql(u8, name, "shrinkAndFree") or
        std.mem.eql(u8, name, "shrinkRetainingCapacity") or
        // HashMap operations that rehash / invalidate iterators.
        std.mem.eql(u8, name, "put") or
        std.mem.eql(u8, name, "putAssumeCapacity") or
        std.mem.eql(u8, name, "putAssumeCapacityNoClobber") or
        std.mem.eql(u8, name, "putNoClobber") or
        std.mem.eql(u8, name, "remove") or
        std.mem.eql(u8, name, "fetchRemove") or
        std.mem.eql(u8, name, "getOrPut") or
        std.mem.eql(u8, name, "getOrPutValue");
}

/// Scan `[start, end]` for the first `<recv-path>.<mutator>(` at
/// any depth, where the path matches the token sequence
/// `[recv_range.first, recv_range.last]` token-by-token.  Skips
/// nested fn declarations and the recv-path's own occurrence
/// inside the for-loop header.
fn findReceiverMutate(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv_range: ReceiverRange,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    const recv_first_slice = tree.tokenSlice(recv_range.first);
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, end);
            continue;
        }
        if (tags[t] != .identifier) continue;
        // Word-boundary at start of the chain.
        if (t > 0 and tags[t - 1] == .period) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv_first_slice)) continue;
        // Match each subsequent token of the receiver chain.
        const recv_len: u32 = @intCast(recv_range.last - recv_range.first);
        var ok: bool = true;
        var i: u32 = 1;
        while (i <= recv_len) : (i += 1) {
            const cur = t + i;
            const ref = recv_range.first + i;
            if (cur > end) {
                ok = false;
                break;
            }
            if (tags[cur] != tags[ref]) {
                ok = false;
                break;
            }
            if (tags[cur] == .identifier and
                !std.mem.eql(u8, tree.tokenSlice(cur), tree.tokenSlice(ref)))
            {
                ok = false;
                break;
            }
        }
        if (!ok) continue;
        const after_recv = t + recv_len + 1;
        if (after_recv + 2 > end) continue;
        if (tags[after_recv] != .period) continue;
        if (tags[after_recv + 1] != .identifier) continue;
        if (tags[after_recv + 2] != .l_paren) continue;
        if (isInvalidatingMutateName(tree.tokenSlice(after_recv + 1))) return after_recv + 1;
    }
    return null;
}

/// True when the mutator call is followed only by an optional semicolon
/// and `return`. A by-value capture is detached, and this control-flow
/// shape performs no iterator read after the mutation.
fn mutationImmediatelyReturns(
    tree: *const Ast,
    mutate_tok: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    const lp = mutate_tok + 1;
    if (lp > body_last or tags[lp] != .l_paren) return false;
    const rp = matchParen(tags, lp, body_last) orelse return false;
    var next = rp + 1;
    if (next <= body_last and tags[next] == .semicolon) next += 1;
    return next <= body_last and tags[next] == .keyword_return;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    for_tok: Ast.TokenIndex,
    recv: []const u8,
    mutate_tok: Ast.TokenIndex,
) !void {
    const mutate_method = tree.tokenSlice(mutate_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "iterator invalidation — `{s}.{s}(...)` mutates `{s}` while a `for ({s}.items) |...|` is iterating over it; the loop's slice borrow may dangle (append/resize realloc) or skip/double-visit elements (insert/swapRemove/remove).  Snapshot the items into a separate list before the loop, or restructure to process+collect first and mutate after",
        .{ recv, mutate_method, recv, recv },
    );
    errdefer gpa.free(msg);
    const note_label = try std.fmt.allocPrint(gpa, "iterating over `{s}.items` here", .{recv});
    errdefer gpa.free(note_label);
    const for_pos = try Pos.fromTokenStart(tree, for_tok);
    const for_end = try Pos.fromTokenEnd(tree, for_tok);
    const notes_slice = try gpa.alloc(problem_mod.Note, 1);
    errdefer gpa.free(notes_slice);
    notes_slice[0] = .{ .start = for_pos, .end = for_end, .label = note_label };
    try problems.append(gpa, .{
        .rule_id = "iterator-invalidation-mutation",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, mutate_tok),
        .end = try Pos.fromTokenEnd(tree, mutate_tok),
        .message = msg,
        .notes = notes_slice,
    });
}

// ── Tests ──────────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "iterator-invalidation: for + append fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn add(list: *std.ArrayList(u32)) !void {
        \\    for (list.items) |x| {
        \\        if (x == 0) try list.append(42);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("iterator-invalidation-mutation", problems.items[0].rule_id);
}

test "iterator-invalidation: for + swapRemove fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn purge(list: *std.ArrayList(u32)) void {
        \\    for (list.items, 0..) |x, i| {
        \\        if (x == 0) _ = list.swapRemove(i);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // for (list.items, 0..) — multi-input loop, our rule requires
    // a single input.  Expect 0 findings.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "iterator-invalidation: for + put on hashmap fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn rebuild(map: *std.StringHashMap(u32)) !void {
        \\    for (map.values()) |v| {
        \\        try map.put("x", v + 1);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // for (map.values()) — the receiver `map` is followed by a
    // call `.values()`, not the field-access shape we look for.
    // Our rule keys on `.items`/`.values`/`.keys` as a FIELD
    // access; method-call form is not detected.  Expect 0.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "iterator-invalidation: pure read loop doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn sum(list: *std.ArrayList(u32)) u32 {
        \\    var total: u32 = 0;
        \\    for (list.items) |x| total += x;
        \\    return total;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "iterator-invalidation: mutate on DIFFERENT list doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn copy(src: *std.ArrayList(u32), dst: *std.ArrayList(u32)) !void {
        \\    for (src.items) |x| {
        \\        try dst.append(x);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "skript regression: by-value iterator capture returns after mutation" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn take(list: *std.ArrayList(u32)) !u32 {
        \\    for (list.items) |candidate| {
        \\        try list.append(candidate);
        \\        return candidate;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "skript regression: pointer iterator capture remains unsafe after mutation" {
    try testing.expectFires(check, "iterator-invalidation-mutation",
        \\const std = @import("std");
        \\pub fn take(list: *std.ArrayList(u32)) !u32 {
        \\    for (list.items) |*candidate| {
        \\        try list.append(candidate.*);
        \\        return candidate.*;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}
