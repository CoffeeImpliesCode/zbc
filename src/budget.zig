//! Analysis-budget accounting.
//!
//! Every bounded walk in zbc gives up by returning
//! `error.AnalysisBudgetExceeded`.  On its own that error says only
//! THAT a limit was hit — not which one, and not where.  A project with
//! one oversized file therefore cannot tell a 64-deep expression nest
//! apart from a worklist that failed to converge, and both look
//! identical in the CLI's `cannot analyze` line.
//!
//! This module records the missing half: the limit that tripped, the
//! bound in force, the value the counter reached, and the enclosing
//! function plus source position.  Call sites use `fail` to record and
//! return in one step; the CLI claims the record with `take`.
//!
//! The record is thread-local because zbc analyses files on a worker
//! pool.  The function name is stored inline rather than borrowed: the
//! AST that owns the name is released before the CLI prints, so a
//! borrowed slice would dangle by then.

const std = @import("std");

/// The bounded walk that ran out of budget.  One variant per limit, so
/// the reported cap is derived from the same enum the call site uses —
/// the diagnostic cannot name a limit the analyzer does not enforce.
pub const Limit = enum {
    /// `classifyExpr` expression-nesting depth.
    expr_classify_depth,
    /// `booleanValue` unwinding through `!` / comparison chains.
    boolean_unwind,
    /// `BorrowIterator` expression-walk frame depth.
    borrow_walk_depth,
    /// `BorrowIterator` nodes visited within one expression.
    borrow_walk_nodes,
    /// `FileCache` address-use walk frame depth.
    address_use_depth,
    /// `FileCache` address-use nodes visited in one file.
    address_use_nodes,
    /// Worklist block visits per function.
    block_visits,
    /// Worklist non-mergeable path states per basic block.
    path_states,
    /// `memset_undef_after_len_truncation` AST walk: frame depth of the
    /// explicit iterator stack.
    memset_walk_depth,
    /// `value_range` oracle: analysis steps spent in one query.
    numeric_oracle_steps,
    /// `value_range` oracle: frames a recursive descent may take.
    numeric_oracle_depth,
    /// `value_range` oracle: rounds a bounded fixpoint may run.
    numeric_oracle_fold,
    /// `FileCache` demand-driven grow fold: semantic graph work one
    /// outermost demand query may spend.
    grow_fold_work,
    /// `FileCache` demand-driven grow fold: declarations being folded at
    /// once, each of which is a distinct one rather than a repetition.
    grow_fold_depth,
    /// `return_arraylist_items` arena proof: the real work one file may
    /// spend proving a returned `.items` slice is arena-backed —
    /// declarations indexed, lookups answered and nodes walked.
    arena_proof_steps,
    /// `index_minus_one_without_zero_guard`: how far the rule peels the
    /// transparent wrappers — casts, groupings, `@as` — between a
    /// subscript and the subtraction it must see.  Each wrapper peeled is
    /// real work, so the peel gives up through this limit rather than
    /// answering without having looked.
    index_minus_one_peel_depth,
    /// `value_range` oracle: actual caller sites a length proof may inspect.
    numeric_oracle_callers,
    /// `call_effects.Scan`: iterator frames within one actual function body.
    readonly_call_depth,
    /// `call_effects.Scan`: AST nodes visited within one actual function body.
    readonly_call_nodes,
    /// Shared AST work spent proving storage disjointness at one call site.
    storage_alias_work,
    /// Shared semantic work spent projecting an actual call's returned storage.
    return_storage_work,

    /// Human-readable name of the cap, for the CLI diagnostic.
    pub fn label(limit: Limit) []const u8 {
        return switch (limit) {
            .expr_classify_depth => "classifyExpr depth",
            .boolean_unwind => "booleanValue unwind",
            .borrow_walk_depth => "borrow-walk depth",
            .borrow_walk_nodes => "borrow-walk nodes",
            .address_use_depth => "address-use walk depth",
            .address_use_nodes => "address-use walk nodes",
            .block_visits => "block visits",
            .path_states => "path states per block",
            .memset_walk_depth => "memset walk depth",
            .numeric_oracle_steps => "numeric oracle steps",
            .numeric_oracle_depth => "numeric oracle depth",
            .numeric_oracle_fold => "numeric oracle fold",
            .grow_fold_work => "grow fold work",
            .grow_fold_depth => "grow fold depth",
            .arena_proof_steps => "arena proof steps",
            .index_minus_one_peel_depth => "index-minus-one peel depth",
            .numeric_oracle_callers => "numeric oracle callers",
            .readonly_call_depth => "readonly-call body depth",
            .readonly_call_nodes => "readonly-call body nodes",
            .storage_alias_work => "storage-alias query work",
            .return_storage_work => "returned-storage query work",
        };
    }
};

/// The bound a bounded walk hit, recorded at the site that hit it.  It lives
/// here rather than in each module because the record has to be writable from
/// wherever the bound is actually enforced: an evaluator that declines to
/// descend names the DEPTH bound, not the step budget, and only a shared
/// vocabulary keeps those two apart.  `reached` is deliberately not part of
/// it — every bound here is checked before it is used, so the value a tripped
/// bound reached is the bound itself.
pub const Stop = struct { limit: Limit, cap: u32 };

/// The error every bounded walk returns.  Named so `fuzz_check.zig` and
/// the library's own catches keep matching it unchanged.
pub const BudgetError = error{AnalysisBudgetExceeded};

/// Fixed-capacity function name.  Truncating is honest: an identifier
/// longer than this is not what a reader needs to see in a budget
/// diagnostic, and the byte offset still pinpoints the function.
pub const NameBuf = struct {
    bytes: [64]u8 = @splat(0),
    len: u8 = 0,

    pub fn slice(self: *const NameBuf) []const u8 {
        return self.bytes[0..self.len];
    }

    pub fn set(self: *NameBuf, name: []const u8) void {
        const copied = @min(name.len, self.bytes.len);
        @memcpy(self.bytes[0..copied], name[0..copied]);
        self.len = @intCast(copied);
    }
};

/// What a bounded walk was doing when it gave up.
pub const Diagnostic = struct {
    limit: Limit,
    /// The bound that was in force.
    limit_value: u32,
    /// What the counter had reached when it tripped.
    reached: u32,
    /// Byte offset of the site.  0 when unknown.
    byte: u32 = 0,
    /// 1-indexed; 0 when the producer had no line table.
    line: u32 = 0,
    column: u32 = 0,
    function: NameBuf = .{},
};

/// The first failure recorded on this thread since the last `take` or
/// `clear`.  First-wins: a walk that gives up keeps unwinding and may
/// trip further limits, but the site where it first stopped is the one
/// that explains the rest.
threadlocal var pending: ?Diagnostic = null;

/// Record `diagnostic` and return the error callers propagate.  Only
/// the first failure on a thread is kept.
pub fn fail(diagnostic: Diagnostic) BudgetError {
    if (pending == null) pending = diagnostic;
    return error.AnalysisBudgetExceeded;
}

/// The unclaimed failure on this thread, if any.
pub fn peek() ?Diagnostic {
    return pending;
}

/// Return and clear the pending failure.  The CLI calls this on the
/// worker thread that produced the error, before the pool is joined.
pub fn take() ?Diagnostic {
    const result = pending;
    pending = null;
    return result;
}

/// Drop any pending failure.  Called at the start of each file so a
/// worker that just succeeded cannot leak its predecessor's record.
pub fn clear() void {
    pending = null;
}

/// 1-indexed line and column of `byte` within `source`.  Allocation
/// free and only ever reached on the failure path, so a linear scan is
/// cheaper than materialising a line-offset table for a file that is
/// about to be reported as unanalyzable.
pub fn lineCol(source: []const u8, byte: u32) struct { line: u32, column: u32 } {
    const limit: usize = @min(byte, source.len);
    var line: u32 = 1;
    var line_start: usize = 0;
    for (source[0..limit], 0..) |char, index| {
        if (char == '\n') {
            line += 1;
            line_start = index + 1;
        }
    }
    return .{ .line = line, .column = @intCast(limit - line_start + 1) };
}

// ── Tests ──────────────────────────────────────────────────

test "fail records the first limit and take clears it" {
    clear();
    try std.testing.expect(peek() == null);
    // `fail` both records and returns, so the caller propagates the same
    // error its own callers already match on.
    try std.testing.expectEqual(error.AnalysisBudgetExceeded, fail(.{
        .limit = .block_visits,
        .limit_value = 10,
        .reached = 10,
        .function = blk: {
            var name: NameBuf = .{};
            name.set("first");
            break :blk name;
        },
    }));
    fail(.{ .limit = .path_states, .limit_value = 64, .reached = 64 }) catch {};
    const taken = take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(Limit.block_visits, taken.limit);
    try std.testing.expectEqual(@as(u32, 10), taken.limit_value);
    try std.testing.expectEqual(@as(u32, 10), taken.reached);
    try std.testing.expectEqualStrings("first", taken.function.slice());
    try std.testing.expect(peek() == null);
    try std.testing.expect(take() == null);
}

test "NameBuf truncates rather than overflowing" {
    var name: NameBuf = .{};
    const long = "x" ** 200;
    name.set(long);
    try std.testing.expectEqual(@as(usize, 64), name.slice().len);
    name.set("short");
    try std.testing.expectEqualStrings("short", name.slice());
    name.set("");
    try std.testing.expectEqualStrings("", name.slice());
}

test "lineCol reports 1-indexed line and column" {
    // Byte 14 is the newline that ends line 1; byte 15 starts line 2.
    const source = "fn a() void {}\nfn b() void {}\n";
    try std.testing.expectEqual(@as(u32, 1), lineCol(source, 0).line);
    try std.testing.expectEqual(@as(u32, 1), lineCol(source, 0).column);
    // A newline byte still belongs to the line it terminates.
    try std.testing.expectEqual(@as(u32, 1), lineCol(source, 14).line);
    try std.testing.expectEqual(@as(u32, 15), lineCol(source, 14).column);
    try std.testing.expectEqual(@as(u32, 2), lineCol(source, 15).line);
    try std.testing.expectEqual(@as(u32, 1), lineCol(source, 15).column);
    try std.testing.expectEqual(@as(u32, 9), lineCol(source, 23).column);
    // A byte past EOF clamps instead of reading out of bounds.
    const past = lineCol(source, 10_000);
    try std.testing.expectEqual(@as(u32, 3), past.line);
    try std.testing.expectEqual(@as(u32, 1), past.column);
}
