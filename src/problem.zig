//! Shared output type for Layer 1 (annotation-hygiene) lint rules.
//!
//! Mirrors zlinter's `LintProblem` shape so we can swap to the zlinter
//! framework later without rewriting rules. For now we self-host —
//! zlinter requires Zig 0.16.0 release / 0.17.0-dev (pulls ZLS), and
//! we're on 0.16.0-dev.3028.

const std = @import("std");

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

/// A reported source position.
///
/// Requires a valid AST with source shorter than `maxInt(u32)` bytes.
/// Analyzer entry points reject wider buffers before parsing or copying;
/// `FileCache.init` checks caller-supplied ASTs. The strict bound preserves
/// 1-indexed lines and columns, whereas AST byte offsets alone also permit
/// a source of exactly `maxInt(u32)` bytes.
pub const Pos = struct {
    /// 1-indexed line number.
    line: u32,
    /// 1-indexed column.
    column: u32,
    /// Byte offset into the source file.
    byte: u32,

    fn assertSourceFits(tree: *const std.zig.Ast) void {
        std.debug.assert(tree.source.len < std.math.maxInt(u32));
    }

    pub fn fromTokenStart(tree: *const std.zig.Ast, tok: std.zig.Ast.TokenIndex) Pos {
        assertSourceFits(tree);
        const starts = tree.tokens.items(.start);
        const loc = tree.tokenLocation(0, tok);
        return .{
            .line = @intCast(loc.line + 1),
            .column = @intCast(loc.column + 1),
            // The byte offset is the token's own, already `u32`.
            .byte = starts[tok],
        };
    }

    pub fn fromTokenEnd(tree: *const std.zig.Ast, tok: std.zig.Ast.TokenIndex) Pos {
        assertSourceFits(tree);
        const starts = tree.tokens.items(.start);
        const length = std.math.cast(u32, tree.tokenSlice(tok).len) orelse unreachable;
        const end = starts[tok] + length;
        const loc = tree.tokenLocation(0, tok);
        return .{
            .line = @intCast(loc.line + 1),
            // The end's column on the start's line: both are offsets
            // into the same buffer, so their difference is a column.
            .column = @intCast(end - loc.line_start + 1),
            .byte = end,
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

test "diagnostic token ends exclude inter-token whitespace and comments" {
    const allocator = std.testing.allocator;
    const source = "const alpha = 1 /* gap */ ;";
    var tree = try std.zig.Ast.parse(allocator, source, .zig);
    defer tree.deinit(allocator);

    const end = Pos.fromTokenEnd(&tree, 3);
    try std.testing.expectEqual(Pos{ .line = 1, .column = 16, .byte = 15 }, end);
}
