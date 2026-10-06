//! Which AST nodes the numeric oracle's WHOLE-FILE questions can be about.
//!
//! Both sides of the numeric analysis need this one answer and neither may own
//! it: `cache/file_cache.zig` builds the per-file index from it, and
//! `flow/value_range.zig` reads that index.  Putting it in either of those
//! would make one import the other, and putting it in both would let the two
//! lists drift — the file cache would keep indexing tags the oracle never asks
//! about, or stop indexing one it does, and neither would notice.
//!
//! So it lives here, importing nothing but the standard library's `Ast`.  This
//! module must stay that way: it is on the import path of the file cache, so a
//! dependency on anything under `src/` from here would close a cycle.
//!
//! WHAT THE INDEX IS FOR
//!
//! A rule asks the numeric oracle once per expression it has to judge, and each
//! of those asks the oracle to walk a function body.  Several of the questions
//! that walk answers are about the FILE rather than the body — which `fn_decl`
//! owns this body, which blocks enclose a token, which `test_decl` a call sits
//! in, where the `comptime` audits are, and which nodes a body's escape roots
//! are — and each of them used to walk the whole node array again, once per
//! query.  A loop-heavy file therefore paid for the whole node table once per
//! expression.
//!
//! Every one of those questions switches on the node's tag before it does
//! anything else, so a node of any other tag cannot be one it can answer
//! about.  `isIndexedTag` is that filter: indexing by it makes the per-file
//! index SPARSE, so the table costs memory and iteration proportional to what
//! is actually asked about rather than to the size of the file.
//!
//! ORDER
//!
//! Neither of these predicates says anything about ORDER, and the callers must
//! not infer any.  The consumers need the node array's own order — resolving a
//! `p = q` pointer chain reads the target `q` was already given, and a loop
//! scan gives up on the first diverting node it meets — so an index built with
//! `isIndexedTag` must keep the nodes in the order the array printed them.
//! Filtering is what makes the index sparse; reordering is not.

const std = @import("std");
const Ast = std.zig.Ast;

/// Is a node of this tag one a whole-file numeric question can be ABOUT?
///
/// The union of the tags those questions switch on: block nodes, `fn_decl`,
/// `test_decl`, `comptime`, `address_of`, the three `var`/`const` declaration
/// tags, and the assign family.  Everything else in a file's node array is
/// skipped by all of them before they look at anything.
///
/// NOT here: the loop-diverting tags.  The loop-candidate scan reads the raw
/// node array on purpose — it charges a step for every node its loop body
/// contains before deciding whether the node is interesting, and that charge is
/// what the query's step counter and the bound its diagnostic reports are made
/// of — so it has to see the nodes this filter would drop.  That is a property
/// of the CALLER's budget accounting, not of the index, which is why the
/// exclusion is documented here rather than enforced.
pub fn isIndexedTag(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        .fn_decl,
        .test_decl,
        .@"comptime",
        .address_of,
        .simple_var_decl,
        .local_var_decl,
        .aligned_var_decl,
        => true,
        // The assign family is already enumerated once, by
        // `isScalarAssignTag`; re-listing twenty spellings of "=" here is the
        // way the two lists drift apart.
        else => isScalarAssignTag(tag),
    };
}

/// Is this an assignment whose left-hand side is a plain scalar?
///
/// One list, read by both the index (through `isIndexedTag`) and the loop
/// scan, because a tag the index carries but the scan does not know about — or
/// the reverse — is a silent disagreement about which nodes a query is about.
pub fn isScalarAssignTag(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .assign,
        .assign_add,
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_sub,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_and,
        .assign_bit_xor,
        .assign_bit_or,
        .assign_mul_wrap,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        => true,
        else => false,
    };
}
