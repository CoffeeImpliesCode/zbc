//! Shared output type for Layer 1 (annotation-hygiene) lint rules.
//!
//! Mirrors zlinter's `LintProblem` shape so we can swap to the zlinter
//! framework later without rewriting rules. For now we self-host —
//! zlinter requires Zig 0.16.0 release / 0.17.0-dev (pulls ZLS), and
//! we're on 0.16.0-dev.3028.
//!
//! `Pos` constructors read positions from the original AST source and
//! return `error.SourceTooWide` before token reads when its byte length
//! cannot leave room for a 1-indexed end column. Coordinate additions
//! and narrowing also return that error; no position is truncated.

const std = @import("std");
const budget_mod = @import("budget.zig");

pub const Severity = enum { off, warning, @"error" };

/// Three-valued confirmation status (issue #18 — a truth oracle for
/// findings).  Static analysis always emits `.unknown`: the rule fired,
/// but nothing has proven the finding true or false.  A downstream
/// confirmation oracle (e.g. the fuzz-harness runner) may upgrade it to:
///   - `.confirmed` — a real bug, reproduced dynamically; `witness`
///     holds the input that triggers it.
///   - `.refuted`   — proven impossible by a SOUND static argument.
///
/// Asymmetry that matters: a fuzzer that fails to crash does NOT justify
/// `.refuted` — absence of a witness is not a proof of safety, so an
/// unconfirmed finding stays `.unknown`, never auto-`.refuted`.
pub const Verdict = enum { unknown, confirmed, refuted };

pub const Pos = struct {
    /// 1-indexed line number.
    line: u32,
    /// 1-indexed column.
    column: u32,
    /// Byte offset into the source file.
    byte: u32,

    /// Position in the original AST source. `tok` must belong to `tree`.
    /// Refuses an unrepresentable source before reading any token.
    pub fn fromTokenStart(tree: *const std.zig.Ast, tok: std.zig.Ast.TokenIndex) error{SourceTooWide}!Pos {
        if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
        const loc = tree.tokenLocation(0, tok);
        const line = std.math.cast(u32, loc.line) orelse return error.SourceTooWide;
        const column = std.math.cast(u32, loc.column) orelse return error.SourceTooWide;
        return .{
            .line = std.math.add(u32, line, 1) catch return error.SourceTooWide,
            .column = std.math.add(u32, column, 1) catch return error.SourceTooWide,
            .byte = tree.tokens.items(.start)[tok],
        };
    }

    /// Exclusive end in the original AST source. `tok` must belong to `tree`.
    /// The source bound leaves room for the 1-indexed column past its end.
    pub fn fromTokenEnd(tree: *const std.zig.Ast, tok: std.zig.Ast.TokenIndex) error{SourceTooWide}!Pos {
        if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
        const start = tree.tokens.items(.start)[tok];
        const slice_len = std.math.cast(u32, tree.tokenSlice(tok).len) orelse return error.SourceTooWide;
        const end_byte = std.math.add(u32, start, slice_len) catch return error.SourceTooWide;
        const loc = tree.tokenLocation(0, tok);
        const line = std.math.cast(u32, loc.line) orelse return error.SourceTooWide;
        const column = std.math.cast(u32, loc.column) orelse return error.SourceTooWide;
        const column_end = std.math.add(u32, column, slice_len) catch return error.SourceTooWide;
        return .{
            .line = std.math.add(u32, line, 1) catch return error.SourceTooWide,
            .column = std.math.add(u32, column_end, 1) catch return error.SourceTooWide,
            .byte = end_byte,
        };
    }
};

/// Secondary diagnostic span — a related event (e.g. "value freed
/// here") that the primary report should point at.  Rendered below
/// the primary span in rich format.  Label text is owned.
pub const Note = struct {
    start: Pos,
    end: Pos,
    label: []const u8,
};

pub const Problem = struct {
    rule_id: []const u8,
    severity: Severity,
    start: Pos,
    end: Pos,
    /// Owned by the problem (caller dupes before append).
    message: []const u8,
    /// Optional secondary spans.  Owned (each `label`) plus the slice
    /// itself.  Empty slice == no notes; `&.{}` is fine.
    notes: []Note = &.{},
    /// Confirmation status (issue #18).  Defaults to `.unknown`; only a
    /// confirmation oracle sets `.confirmed` / `.refuted`.  See Verdict.
    verdict: Verdict = .unknown,
    /// Reproducing input that confirmed this finding, set together with
    /// `verdict == .confirmed`.  Owned (caller dupes).  Null otherwise.
    witness: ?[]const u8 = null,

    pub fn deinit(self: *Problem, gpa: std.mem.Allocator) void {
        gpa.free(self.message);
        for (self.notes) |n| gpa.free(n.label);
        if (self.notes.len > 0) gpa.free(self.notes);
        if (self.witness) |w| gpa.free(w);
    }
};

/// One part of a file's analysis that stopped on an analysis budget.
/// Findings from that part are absent; every other part completed.
pub const Incomplete = struct {
    pub const Kind = enum {
        /// Lowering or the flow check of one function.
        function,
        /// One pattern rule.
        rule,
        /// The file-level summary pass for one function.
        summary,
    };

    kind: Kind,
    /// Function name or rule id. Owned.
    name: []const u8,
    /// The limit that tripped. Null when the walk that gave up recorded none.
    budget: ?budget_mod.Diagnostic,

    pub fn deinit(self: *Incomplete, gpa: std.mem.Allocator) void {
        gpa.free(self.name);
    }
};

/// Copy `name` and append it as an incomplete part.
pub fn appendIncomplete(
    gpa: std.mem.Allocator,
    list: *std.ArrayListUnmanaged(Incomplete),
    kind: Incomplete.Kind,
    name: []const u8,
    budget: ?budget_mod.Diagnostic,
) std.mem.Allocator.Error!void {
    const owned = try gpa.dupe(u8, name);
    errdefer gpa.free(owned);
    try list.append(gpa, .{ .kind = kind, .name = owned, .budget = budget });
}

/// Free and drop every Problem at index `len` and above.
pub fn truncateProblems(gpa: std.mem.Allocator, list: *std.ArrayListUnmanaged(Problem), len: usize) void {
    std.debug.assert(len <= list.items.len);
    for (list.items[len..]) |*problem| problem.deinit(gpa);
    list.shrinkRetainingCapacity(len);
}

test "diagnostic token ends exclude inter-token whitespace and comments" {
    const allocator = std.testing.allocator;
    const source = "const alpha = 1 /* gap */ ;";
    var tree = try std.zig.Ast.parse(allocator, source, .zig);
    defer tree.deinit(allocator);

    const end = try Pos.fromTokenEnd(&tree, 3);
    try std.testing.expectEqual(Pos{ .line = 1, .column = 16, .byte = 15 }, end);
}
