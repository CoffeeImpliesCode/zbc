//! `const gop = try map.getOrPut(key);` followed by `gop.value_ptr.*`
//! used as a READ before checking `gop.found_existing`.
//!
//! When `found_existing == false` the map inserted a new slot and
//! `value_ptr.*` is uninitialised; reading it is undefined behaviour.
//! Write-only access (`gop.value_ptr.* = value;`) is safe without the
//! check.
//!
//! Detection (per-fn token walk):
//!   1. Find `const/var <name> = [try] <chain>.getOrPut[...](...)`.
//!   2. After the statement's `;`, scan for `<name>.value_ptr`.
//!   3. Track whether `<name>.found_existing` was referenced first.
//!   4. If `value_ptr` is accessed as a READ (not a plain `= ...`
//!      assignment) before any `found_existing` reference, fire.
//!
//! Compound assignments (`+= -= |= &=`) DO read the current value
//! and are also flagged.
//!
//! Suppressed when:
//!   - `<name>.found_existing` appears anywhere before the read.
//!   - The access is a bare write: `<name>.value_ptr.* = <expr>;`.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const skipNestedFn = tokens.skipNestedFn;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .getorput_unguarded_value_read)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

/// getOrPut variants we recognise.  `getOrPutValue` and the `AssumeCapacity`
/// variants do NOT return `found_existing` / `value_ptr` — they return the
/// value directly.  Only the variants that return a GetOrPutResult need
/// to be checked.
fn isGetOrPutName(s: []const u8) bool {
    return std.mem.eql(u8, s, "getOrPut") or
        std.mem.eql(u8, s, "getOrPutAdapted") or
        std.mem.eql(u8, s, "getOrPutContext") or
        std.mem.eql(u8, s, "getOrPutContextAdapted");
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
    while (t + 4 <= last) : (t += 1) {
        // Skip nested fn bodies.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Look for the getOrPut call-site:
        //   `... .getOrPut( ...`
        // The binding name is found by walking backward from `.getOrPut`.
        if (tags[t] != .identifier) continue;
        if (!isGetOrPutName(tree.tokenSlice(t))) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        if (t + 1 > last or tags[t + 1] != .l_paren) continue;

        // Walk backward from `t-2` (before the `.`) to find the `=` of the
        // binding statement, then extract the binding identifier.
        const binding: []const u8 = findBindingName(tree, t - 1, first) orelse continue;

        // Find the `;` that ends the getOrPut statement.
        const semi = tokens.findStmtSemicolon(tags, t, last) orelse continue;

        // Scan from `semi+1` forward for unguarded reads of `binding.value_ptr`.
        try scanForUnguardedRead(gpa, tree, binding, semi + 1, last, problems);
    }
}

/// Walk backward from `dot_pos` (the `.` before `getOrPut`) looking for
/// `const/var <name> = [try]`.  Returns the binding name slice on success.
fn findBindingName(
    tree: *const Ast,
    dot_pos: Ast.TokenIndex,
    first: Ast.TokenIndex,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    // Walk backward, tracking nesting depth for `()[]{}`.
    // Stop when we find `=` at depth 0.
    var depth: u32 = 0;
    var i: Ast.TokenIndex = dot_pos;
    while (i > first) : (i -= 1) {
        switch (tags[i]) {
            .r_paren, .r_bracket, .r_brace => depth += 1,
            .l_paren, .l_brace, .l_bracket => {
                if (depth == 0) return null;
                depth -= 1;
            },
            .equal => {
                if (depth == 0) break;
            },
            else => {},
        }
    } else return null;
    // `i` is now at `=`.  Walk further back to find `const/var <name> =`.
    // Skip `try` or `comptime` keywords.
    // i == the `=` token.  Check i-1 and i-2.
    if (i < 2) return null;
    // Optional `pub` / `const` / `var` before the name.
    const j = i - 1;
    // Skip `try`, `comptime` if they immediately precede `=`? No —
    // `const name = try ...` has tokens: const name = try ...
    // So before `=` is `name` (identifier), before `name` is `const` or `var`.
    if (tags[j] != .identifier) return null;
    const name = tree.tokenSlice(j);
    if (j == 0) return null;
    const before_name = tags[j - 1];
    if (before_name != .keyword_const and before_name != .keyword_var) return null;
    return name;
}

/// From `scan_start` to `last`, look for `<binding>.value_ptr` used as a
/// READ before any `<binding>.found_existing` reference.
fn scanForUnguardedRead(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    binding: []const u8,
    scan_start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    var found_existing_seen = false;

    var t: Ast.TokenIndex = scan_start;
    while (t + 2 <= last) : (t += 1) {
        // Skip nested fn bodies so inner lambdas don't confuse us.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), binding)) continue;
        // Require `.` next.
        if (t + 1 > last or tags[t + 1] != .period) continue;
        // Require identifier after `.`.
        if (t + 2 > last or tags[t + 2] != .identifier) continue;
        const field = tree.tokenSlice(t + 2);

        if (std.mem.eql(u8, field, "found_existing")) {
            found_existing_seen = true;
            continue;
        }

        if (!std.mem.eql(u8, field, "value_ptr")) continue;

        // We have `<binding>.value_ptr`.  Now check what follows.
        // In Zig's tokenizer `.*` is a single `period_asterisk` token —
        // NOT a `.period` + `.asterisk` pair.
        // Safe:   `<binding>.value_ptr.* = <expr>;`  (plain assignment)
        // Unsafe: `<binding>.value_ptr.*` in any other context,
        //         including compound assignments `+= -= |=` etc.
        if (t + 3 > last or tags[t + 3] != .period_asterisk) continue;

        if (found_existing_seen) continue; // already guarded

        // Check what follows the `.*`:
        // `<binding>.value_ptr.* = <non-compound>` → safe (plain write)
        // `<binding>.value_ptr.* <compound_assign>` → unsafe (reads old value)
        // `<binding>.value_ptr.*` anything else → unsafe (read)
        if (t + 4 <= last) {
            const after = tags[t + 4];
            if (after == .equal) continue; // plain assignment — safe
            // Compound assignment reads the old value — flag it.
        }

        // Fire.
        const msg = try std.fmt.allocPrint(
            gpa,
            "`{s}.value_ptr.*` is read before `{s}.found_existing` is checked — when the key was newly inserted, `value_ptr.*` is uninitialised (UB).  Guard the read: `if ({s}.found_existing) {{ … {s}.value_ptr.* … }}`",
            .{ binding, binding, binding, binding },
        );
        errdefer gpa.free(msg);
        try problems.append(gpa, .{
            .rule_id = "getorput-unguarded-value-read",
            .severity = .@"error",
            .start = try Pos.fromTokenStart(tree, t),
            .end = try Pos.fromTokenEnd(tree, t + 3),
            .message = msg,
        });
        // Suppress further reports for this binding in this scope.
        found_existing_seen = true;
    }
}

// ── Tests ──────────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "getorput-unguarded-value-read: unguarded read fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, key: u32) u32 {
        \\    const gop = map.getOrPut(key) catch unreachable;
        \\    return gop.value_ptr.*;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("getorput-unguarded-value-read", problems.items[0].rule_id);
}

test "getorput-unguarded-value-read: guarded by found_existing does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, key: u32) u32 {
        \\    const gop = map.getOrPut(key) catch unreachable;
        \\    if (gop.found_existing) return gop.value_ptr.*;
        \\    gop.value_ptr.* = 0;
        \\    return 0;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "getorput-unguarded-value-read: plain write does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, key: u32) void {
        \\    const gop = map.getOrPut(key) catch unreachable;
        \\    gop.value_ptr.* = 42;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "getorput-unguarded-value-read: compound assign fires (reads old value)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, key: u32) void {
        \\    const gop = map.getOrPut(key) catch unreachable;
        \\    gop.value_ptr.* += 1;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "getorput-unguarded-value-read: found_existing check before read suppresses" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, key: u32) u32 {
        \\    const gop = map.getOrPut(key) catch unreachable;
        \\    if (!gop.found_existing) gop.value_ptr.* = 0;
        \\    return gop.value_ptr.*;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
