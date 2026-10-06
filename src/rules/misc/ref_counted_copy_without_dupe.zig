//! Detects two shapes that duplicate one reference:
//!
//!   * a struct literal field copied from the same-named field of
//!     another struct (`.field = recv.field`) into a declaration that
//!     hands that field back, with no ref-acquire method
//!     (clone/dupeRef/ref/retain/…) called on the source first; and
//!   * a WHOLE owning handle copied out of a by-value parameter —
//!     `pub fn copy(source: Shared) Shared { return source; }`.
//!
//! Both verdicts are read from a DECLARATION, never from a name.
//!
//! Real-world shapes:
//!   oven-sh/bun#30955 — `Blob.name` bitwise-copied without calling
//!   `.dupeRef()`; both the source and the copy call `name.deinit()` →
//!   double-decrement → SIGFPE.
//!   oven-sh/bun#30991 — WTF string ref copied without `ref()`.
//!   oven-sh/bun#30882 — specifier field copied without `dupe_ref()`.
//!
//! Detection — a name-evidence scan, then two independent copy passes:
//!
//!   Pass 1 — evidence collection:
//!     Scan the entire file for calls of the form
//!       `receiver . field_name . <acquire_or_release_method> (`
//!     where acquire methods: clone/dupeRef/ref/retain/dupe/addRef
//!           release methods: deinit/deref/free/release/unref/destroy/drop
//!     For each such `field_name`, record it as "evidenced" — this file
//!     gives that spelling a lifecycle SOMEWHERE.  The observation is
//!     deliberately file-wide and coarse, and it is only ever a
//!     FALLBACK: it decides what to look at when there is no declaration
//!     to read the field through, and never whether a copy is a bug.
//!
//!   Pass 2 — copy check, bound to the destination DECLARATION:
//!     Every struct literal in the file is opened.  Its OWN fields — the
//!     ones at brace depth 1, since a nested literal is a node of its own
//!     and is checked there — are matched against the copy shape
//!       `. dest_field = source_recv . source_field`
//!     with `dest_field == source_field`.  A further access on the right
//!     (`recv.field.clone()`, `recv.field.subfield`) and an ownership MOVE
//!     (the source cleared right after) are excluded.
//!
//!     What the literal CONSTRUCTS decides the outcome, because ownership
//!     is a property of one declaration and not of a spelling.  The name
//!     is bound from the literal's own type expression (`Owner`,
//!     `pkg.Owner`, `Outer.Inner`, at whatever depth it is written), or —
//!     for an anonymous literal (`.{ … }`) — from the context that names
//!     it: the type the enclosing function returns, or the type an
//!     annotated local is declared with.  Nothing else names an anonymous
//!     literal, and the SOURCE's type is never a stand-in for it.
//!
//!     Then the declaration itself answers, with nothing else in the file
//!     consulted:
//!       * it runs a teardown on THAT FIELD — directly
//!         (`self.f.release(…)`), through an optional unwrap
//!         (`self.f.?.release(…)`), or through a value it binds from the
//!         field (`const snap = self.f`, `if (self.f) |snap|`) — so the
//!         copy becomes a second owner of one reference: report;
//!       * it takes the field as a pointer and runs NO protocol on it at
//!         all — a BORROWED VIEW — or hands it to a callee as the
//!         standard allocator BY VALUE, a capability the callee borrows:
//!         stay quiet, nothing is duplicated because nothing will ever be
//!         released;
//!       * it says nothing this rule can read, or there is no destination
//!         to read: the historical verdict stands — a refcounted-ish name
//!         the file evidences somewhere is reported, as it always was.
//!
//!     Binding to the declaration is what keeps this honest in both
//!     directions.  A `Plan` that really releases its `data` must not lend
//!     that verdict to a `View` in the same file that only borrows the
//!     same pointer; and an owning declaration must not be silenced by a
//!     name that looks like a plain value or by a file that happens to
//!     spell no lifecycle call on it anywhere.
//!
//!     What balances the copy comes from the same declaration.  An
//!     acquire on the copy's own source and field, written before it in
//!     the copy's own body, is the fix only where the declaration drives
//!     the field through a reference PROTOCOL of its own; a teardown that
//!     takes the field's storage apart itself, frees its own receiver, or
//!     cannot be read is charged whatever any count says, so an acquire
//!     written on such a field silences a real double free and is not
//!     read as a fix.
//!
//!     The acquire also has to be one the copy cannot be reached
//!     without.  `if (verbose) source.ref.retain(); return source;`
//!     acquires on the paths that take the branch and duplicates the
//!     reference on every other one, so it is no fix for that copy; the
//!     same acquire written in the same branch as the copy is the fix for
//!     that copy and for nothing else.
//!
//!   Pass 3 — whole-value copies, bound to the SOURCE DECLARATION:
//!     One reference is duplicated just as surely by handing the whole
//!     handle on as by spelling a field out of a literal:
//!     `pub fn copy(source: Shared) Shared { return source; }` gives
//!     the caller a second owner of the one reference `Shared` holds.
//!     Every `return <param>;` and every `const|var <name> =
//!     <param>;` whose source is a BY-VALUE parameter of a declaration
//!     that runs a reference protocol on any of its own fields is one
//!     report, and that same declaration decides it: `Shared.deref`
//!     hands the reference its `ref` field holds back, so the copy is a
//!     second owner of one reference.  The destination IS that value —
//!     a `return` hands it to the caller, a binding makes it a second
//!     local — so there is nothing further to read.
//!
//!     Only a parameter is a source.  A by-value parameter is itself
//!     copied into the frame, so the caller still holds the original
//!     and the copy is genuinely a second owner; a local the frame
//!     just built has one owner either way, and `return <local>;` is a
//!     move rather than a duplication.
//!
//!     An acquire that reaches the field the copy duplicates —
//!     `source.ref.retain();` before the return, or
//!     `source.ref.?.retain();` for an optional field — is the fix for
//!     that copy, and keeps it quiet.  It has to be a CALL on that exact
//!     source and field: a method taken as a value
//!     (`const dup = source.ref.clone;`), a member of the field spelled
//!     like an acquire (`source.handle.ref.retain()`), a member of
//!     another value named after the parameter
//!     (`wrapper.source.ref.retain()`) and a `defer`red acquire each
//!     balance nothing here — whatever the `defer` wraps, since the
//!     statement runs when its scope exits rather than where it is
//!     written.
//!
//!     Reaching the copy is part of it: a conditional acquire whose
//!     branch ENDS before the copy — `if (keep) source.ref.retain();` in
//!     front of an unconditional `return source;`, one arm of an `if`
//!     beside the other, a `switch` prong beside its neighbour, a loop
//!     that may run zero times — duplicates nothing and balances nothing,
//!     while an acquire written in the same branch as the copy reaches
//!     that copy on every path that makes it.
//!
//!     EVERY field the declaration hands back needs its own acquire, on
//!     the copy's own source: a handle that releases `ref` in `deref` and
//!     `tail` in `drop` duplicates two references at one copy, so
//!     acquiring only the field declared first silences half the bug.
//!     Each declared field is therefore read in turn, and the copy is
//!     reported on the field left unacquired — whichever of them that
//!     is, and whichever order they are declared in.
//!
//!     What a declaration hands back is read from the body, so a field
//!     that merely APPEARS in a teardown is not one it owns: an
//!     allocator field a `self.gpa.destroy(self.name)` is made on is the
//!     mechanism that frees `name`, not a reference of its own.  Which
//!     side of such a call carries the payload is the callee's own
//!     declaration — `Node.free` freeing `self.text` gives the head
//!     back, `Allocator.destroy` freeing `ptr` gives the argument —
//!     never the method's name or the field's name.
//!     A callee this rule cannot read — a type reached through an
//!     import it does not resolve, an alias it cannot follow, a type
//!     that declares no such method — charges BOTH sides rather than
//!     picking one, so an imported owning pointer is never declared
//!     borrowed because its teardown could not be opened.  A callee it
//!     CAN open and still cannot follow to a verdict charges both sides
//!     the same way: a teardown forwarded to another method and a
//!     receiver freed through a function pointer are not proof that
//!     the argument is what the call destroys.
//!
//!     The side a field is WRITTEN on decides which proof answers for
//!     it, and only that one.  A receiver's own free is evidence about
//!     the head: it settles nothing about a reference handed to the same
//!     call as an argument, so `Node.free(gpa, other)` freeing
//!     `self.bytes` leaves `other` charged until the callee's own body
//!     shows it handing `other` to something that destroys it.  An
//!     argument this rule cannot place that way is charged as well —
//!     except the standard allocator BY VALUE (`std.mem.Allocator`,
//!     `mem.Allocator`, an alias of either), which a callee receives as
//!     a capability it borrows rather than one it owns.  A POINTER to
//!     that type is not that value: the descriptor it points at is heap
//!     storage somebody owns, so it stays charged with the rest.
//!
//!     What that side is also decides what balances the copy.  An
//!     acquire fixes a duplicated reference only where the declaration
//!     drives the field through a reference PROTOCOL of its own
//!     (`self.f.deref(gpa)`); a field handed to something that frees it
//!     outright (`self.gpa.destroy(self.f)`) is destroyed whatever a
//!     count says, so an acquire on it silences a real double free and
//!     is not read as a fix.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const file_model_mod = @import("../../model/file_model.zig");
const project_cache_mod = @import("../../cache/project_cache.zig");
const local_bindings = @import("../../model/local_bindings.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const std_type_query = @import("../../model/std_type_query.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ref-counted-copy-without-dupe";

/// Field name substrings that suggest the field holds a refcounted
/// or heap-owned value.
const refcounted_substrings = [_][]const u8{
    "name", "str", "string", "ref", "handle", "buf", "data", "content",
};

/// The declaration a struct literal constructs, with the tree it was
/// declared in — the analysed file for a type bound here, the importing
/// file's model for one reached through an import.
const DestType = struct {
    tree: *const Ast,
    info: *const file_model_mod.TypeInfo,
};

/// What the destination DECLARATION does with the field being copied
/// into it, read from that declaration and from nothing else — not
/// from the field's spelling, and not from a lifecycle call some other
/// type in the file happens to make on the same name.
const FieldVerdict = union(enum) {
    /// Nothing provable: no destination bound, no field of it, or a
    /// destination that runs no protocol on the field and declares no
    /// pointer either.  The coarse name-and-evidence reading answers
    /// this one, as it always has.
    unknown,
    /// The declaration never gives the field back: a borrowed view, or
    /// a field handed to a callee as the standard allocator BY VALUE —
    /// a capability the callee borrows.  Copying into it duplicates
    /// nothing and is quiet whatever else the file does.
    borrowed,
    /// The declaration hands the field back, and `payload` is what that
    /// teardown does with it.  Only a `.protocol` payload is balanced
    /// by an acquire on the field.
    owned: Payload,
};

/// State threaded through the copy check.
const CheckState = struct {
    problems: *std.ArrayListUnmanaged(Problem),
    /// Field names for which at least one acquire OR release call was
    /// found in the file.  This is the COARSE fallback for a literal
    /// whose destination declaration this rule cannot bind: a bound
    /// destination is decided by that declaration alone, so a field
    /// this map never saw is still read through the protocol its
    /// declaration runs on it.
    evidenced: *const std.StringHashMap(void),
    cache: *file_cache_mod.FileCache,
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ref_counted_copy_without_dupe)) return;

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

    var state = CheckState{ .problems = problems, .evidenced = &evidenced, .cache = cache };

    // ── Pass 3: whole-value copies ──────────────────────────────────────
    // Its evidence is the SOURCE declaration and never a field spelling,
    // so it stands on its own and is read first.
    try checkWholeValueCopies(gpa, tree, &state);

    // ── Pass 2: struct-literal field copies ─────────────────────────────
    // A literal whose destination this rule CAN bind is decided by that
    // declaration, not by anything else in the file, so a file that
    // evidences no field still has copies to read.  The evidence map is
    // only the fallback for a literal whose destination cannot be bound
    // here, and it no longer decides whether this pass runs at all.
    try checkStructInits(gpa, tree, &state);
}

/// Open every struct literal in the file.  Reading the literal's own
/// fields through the node — rather than through the enclosing fn's
/// tokens — is what makes the destination declaration available, and it
/// also stops a field of a nested literal being read twice.
fn checkStructInits(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    state: *CheckState,
) !void {
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        switch (tree.nodeTag(node)) {
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => try checkStructInit(gpa, tree, node, state),
            else => {},
        }
    }
}

// ── Pass 3: whole-value copies ────────────────────────────────────

/// The reference a whole-value copy of `dest` duplicates: the field
/// whose ownership one of `dest`'s OWN instance methods hands back, and
/// the name of that method.
///
/// `field` is whichever declared field the copy left UNACQUIRED.  A
/// handle may hand back more than one reference — `Shared.deref`
/// releases `ref` and `Shared.drop` releases `tail` — so it is the
/// unacquired one, not the first declared one, that a report names.
///
/// The verdict is the DECLARATION's, never a field's spelling: the name
/// of the field decides nothing here, and a method WITH a receiver is
/// what separates a destructor from a static allocator callback such as
/// `fn free(ctx: *anyopaque, bytes: []u8)`, which frees somebody else's
/// buffer and is nobody's destructor.
const OwnedRef = struct {
    field: []const u8,
    method: []const u8,
    /// What that teardown does with the field, which decides whether an
    /// acquire is the fix this report may name.
    payload: Payload,
};

/// The field of `dest` that a whole-value copy of the by-value parameter
/// `source` duplicates WITHOUT balancing, with the method that hands it
/// back — or null when `dest` runs no reference protocol on any field
/// it declares (a value type, a borrowed view, or a lease that only
/// writes through the pointer it borrows), or when every field it does
/// hand back has its own acquire on the copy's own path in
/// `[body_first, copy_tok]` — written there directly, or through an
/// immutable local bound from it there.
///
/// `body_first` is the first token of the enclosing body — its `{` — and
/// `before_copy` the last token that can still balance the copy: only an
/// acquire WRITTEN BEFORE the copy reaches the second owner it creates,
/// so one written afterwards is a statement the copy can no longer use.
///
/// Reaching the copy is part of that path: an acquire written inside a
/// branch that has ended by the time the copy runs balances nothing,
/// while an acquire written in the same branch as the copy is the fix
/// for that copy and for no other.
///
/// Every declared field is read, never just the first one that looks
/// owned.  `return source;` duplicates one reference for EVERY field the
/// declaration hands back, so an acquire reaching only the field it
/// declares first silences half the defect: `source.ref.retain()` leaves
/// `tail` a second owner of the reference `Shared.drop` releases, which
/// double-frees exactly as `ref` would have.
///
/// Allocation-free and uncapped: the fields are walked in declaration
/// order and the first unacquired one ends the walk, so one copy site
/// reports one finding naming a field that really is unacquired.
fn unacquiredOwnedRef(
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    dest: DestType,
    body_first: Ast.TokenIndex,
    copy_tok: Ast.TokenIndex,
    source: []const u8,
) ?OwnedRef {
    for (dest.info.fields) |*field| {
        const teardown = lifecycleMethodOnField(cache, dest.tree, dest.info, field.name) orelse continue;
        // An acquire balances a copy ONLY when this declaration drives
        // the field through the field's own reference protocol.  A
        // teardown that hands the field's storage to an allocator takes
        // the field apart itself, so a count the second owner would
        // have kept on it is not what decides the second teardown — and
        // a callee this rule cannot read is no proof that the protocol
        // it has not seen is there.
        if (teardown.payload == .protocol) {
            // The acquire has to reach THIS field on THIS source: one on
            // another field, receiver or subpath duplicates nothing here.
            if (hasRefAcquireCall(tree, tags, body_first, copy_tok -| 1, copy_tok, source, field.name)) continue;
            // A wrapper field holds nothing of its own to acquire: the
            // reference it hands back is the one its pointee holds.
            if (leafRefOfField(cache, dest, field)) |leaf| {
                if (hasLeafRefAcquireCall(tree, tags, body_first, copy_tok -| 1, copy_tok, source, field.name, leaf)) continue;
            }
            if (hasAliasRefAcquireCall(
                cache,
                proto,
                body,
                tree,
                tags,
                body_first,
                copy_tok -| 1,
                source,
                field.name,
            )) continue;
        }
        return .{ .field = field.name, .method = teardown.method, .payload = teardown.payload };
    }
    return null;
}

/// True iff `[start, end]` holds an acquire CALL on the LEAF resource a
/// wrapper field is acquired through:
///
///   source . field . leaf . <acquire> (
///   source . field . leaf . ? . <acquire> (
///
/// The receiver is the root of the chain and the call is really called,
/// exactly as in `hasRefAcquireCall`; the only difference is the one
/// extra member, which is a member this rule RESOLVED from the pointee's
/// own declaration rather than from a spelling.
///
/// The copy is at `copy_tok`, and the acquire has to reach it: a call
/// written inside a branch that has ended by then is an acquire on the
/// paths that took that branch and on no other, exactly as in
/// `hasRefAcquireCall`.
fn hasLeafRefAcquireCall(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    copy_tok: Ast.TokenIndex,
    source_recv: []const u8,
    wrapper: []const u8,
    leaf: []const u8,
) bool {
    if (start > end) return false;
    // The shortest shape is `recv . field . leaf . method (`.
    if (end < start + 6) return false;
    var frames: ReachFrames = .{};
    // The window the extents are read over ends at the COPY, not one token
    // short of it: a branch the window cuts off is still open around the
    // copy, and a branch that closed before it would have its `}` in the
    // window to close.
    collectReachFrames(tags, start, copy_tok, &frames);
    var t = start;
    while (t + 6 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), source_recv)) continue;
        if (t != 0 and tags[t - 1] == .period) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), wrapper)) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), leaf)) continue;
        if (tags[t + 5] != .period) continue;
        // `recv . field . leaf . <acquire> (`
        if (tags[t + 6] == .identifier) {
            if (!method_names.isRefAcquireName(tree.tokenSlice(t + 6))) continue;
            if (t + 7 > end) continue;
            if (tags[t + 7] != .l_paren) continue;
            if (deferredCall(tree, t)) continue;
            if (!reachesCopy(&frames, t, copy_tok)) continue;
            return true;
        }
        // `recv . field . leaf . ? . <acquire> (`
        if (tags[t + 6] == .question_mark) {
            if (t + 9 > end) continue;
            if (tags[t + 7] != .period) continue;
            if (tags[t + 8] != .identifier) continue;
            if (!method_names.isRefAcquireName(tree.tokenSlice(t + 8))) continue;
            if (tags[t + 9] != .l_paren) continue;
            if (deferredCall(tree, t)) continue;
            if (!reachesCopy(&frames, t, copy_tok)) continue;
            return true;
        }
    }
    return false;
}

/// The one member a POINTER field is a WRAPPER for, or null when the
/// field is not one.
///
/// `Doc` with `pub fn deinit(self: *Doc, gpa: std.mem.Allocator) void
/// { self.ref.deref(gpa); }` is nothing but a wrapper for `ref`, so a
/// handle holding `doc: *Doc` hands back the reference `doc.ref` holds
/// and `source.doc.ref.retain()` is what balances the copy — however
/// many borrowed fields beside it declare no protocol of their own.  A
/// `Doc` whose `drop` releases `tail` as well is no wrapper around one
/// reference: `source.doc.ref.retain()` acquires one of two, so the
/// copy stays charged on `tail`.
/// The destructor requirement is what separates that wrapper from a
/// handle that only LOOKS like one: `Node` with `pub fn deref(self:
/// *Node, gpa) void { self.ref.deref(gpa); }` has the same shape, but a
/// reference protocol is not a destructor — the node is a reference in
/// its own right, `node.ref` is a second one inside it, and acquiring
/// the second leaves the first doubled.  So `source.handle.ref.retain()`
/// is not read as a fix and the copy stays charged on `.handle`.
///
/// Every part of that verdict is read from the pointee's real
/// declaration and body, never from a spelling and never from how many
/// fields the struct happens to declare: the field's declared type must
/// resolve to a type this file declares, no method of it may hand
/// storage back through an allocator, and the set of members its own
/// methods release must be exactly one pointer.  Two released members,
/// a released member that is not a pointer, a method this rule cannot
/// read, an unresolvable type, or a declaration in another file all
/// return null and leave the copy reported — an unreadable pointee is
/// never turned into a leaf that silences a real duplicate.
fn leafRefOfField(
    cache: *file_cache_mod.FileCache,
    dest: DestType,
    field: *const file_model_mod.FieldInfo,
) ?[]const u8 {
    const pointee = pointeeDeclOfField(cache, dest, field) orelse return null;
    if (pointee.tree != dest.tree) return null;
    if (declaresOwnStorageHandoff(pointee.tree, pointee.info)) return null;

    // The members the pointee's OWN methods release, read method by
    // method: a borrowed allocator, a label or a state word that no
    // method touches is not a second resource and does not count, while
    // a second method releasing a second member is a reference an
    // acquire on the first one cannot reach.
    var leaf: ?[]const u8 = null;
    for (pointee.info.methods) |*m| {
        const receiver = m.receiver orelse continue;
        for (pointee.info.fields) |*member| {
            if (methodReachesField(cache, pointee.tree, pointee.info, m, receiver.name, member.name) == null) continue;
            if (leaf) |reached| {
                if (!std.mem.eql(u8, reached, member.name)) return null;
                continue;
            }
            // A type torn down by a REFERENCE PROTOCOL is a reference in
            // its own right — `Node.deref` gives back what `node.ref`
            // holds and the node itself is the handle the copy
            // duplicates, so `source.handle.ref.retain()` acquires a
            // second reference and leaves the first one doubled.  A
            // WRAPPER is a value that declares nothing of its own and
            // is finished by its own destructor: there, the handle's
            // reference IS the member's, and acquiring it balances the
            // copy.
            if (!isDestructorName(m.name)) return null;
            // A slice, an array or a counted value member is storage in
            // its own right, not a wrapper around a reference.
            if (!declaredPointer(pointee.tree, member)) return null;
            leaf = member.name;
        }
    }
    return leaf;
}

/// True iff `name` is a method its own type tears ITSELF down with, as
/// opposed to one that acts on a reference the type holds.  `deinit`
/// finishes the value it is called on; `deref`, `release` and `unref`
/// give back a reference and leave the value standing.
fn isDestructorName(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "close") or
        std.mem.eql(u8, name, "stop") or
        std.mem.eql(u8, name, "finalize") or
        std.mem.eql(u8, name, "dispose");
}

/// The declaration a pointer FIELD points at, when this file declares
/// it: `*Doc`, `?*const Doc`, `pkg.Doc`.  Null for a non-pointer, an
/// unreadable path, or a type reached through an import — this rule
/// resolves a pointee only in the file it is reading, so a type from
/// another file cannot lend its verdict here.
fn pointeeDeclOfField(
    cache: *file_cache_mod.FileCache,
    dest: DestType,
    field: *const file_model_mod.FieldInfo,
) ?DestType {
    const tags = dest.tree.tokens.items(.tag);
    var count: usize = 0;
    var saw_pointer = false;
    var t = field.type_first;
    while (t <= field.type_last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => {},
            .asterisk => saw_pointer = true,
            .period => {},
            .identifier => {
                // The model's own qualified reader caps the path at
                // eight segments; one more is no path it can resolve,
                // so this declines exactly where the scan it replaces
                // did.
                if (count == 8) return null;
                count += 1;
            },
            else => return null,
        }
    }
    if (!saw_pointer or count == 0) return null;
    const model = cache.fileModel() catch return null;
    // The model's own qualified reader answers from the same declared
    // tokens, following the parent chain outward so a like-named type
    // declared at another depth cannot stand in for this one.
    const info = model.resolveFieldTypeQualifiedTi(dest.info, field.name) orelse return null;
    return .{ .tree = model.tree, .info = info };
}

/// True iff any receiver method of `ti` hands STORAGE back through an
/// allocator with this type or one of its fields as the argument —
/// `gpa.free(self.bytes)`, `gpa.destroy(self)`, `alloc.dealloc(self.buf)`.
/// Such a type owns storage of its own, so its members are independent
/// resources and none of them stands in for the handle.
fn declaresOwnStorageHandoff(
    tree: *const Ast,
    ti: *const file_model_mod.TypeInfo,
) bool {
    for (ti.methods) |*m| {
        if (methodFreesItsReceiver(tree, m)) return true;
    }
    return false;
}

/// True iff `recv` is named inside `[start, end]` — as an argument
/// (`gpa.destroy(self)`) or as the head of one (`gpa.free(self.bytes)`).
fn namesReceiverAt(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
) bool {
    if (start > end) return false;
    var t = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t), recv)) return true;
    }
    return false;
}

/// Open every function in the file and check its whole-value copies.
fn checkWholeValueCopies(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    state: *CheckState,
) !void {
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        try checkFnWholeValueCopies(gpa, tree, state, entry.proto, entry.body);
    }
}

fn checkFnWholeValueCopies(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    state: *CheckState,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
) !void {
    const tags = tree.tokens.items(.tag);
    const body_first = tree.firstToken(body);
    const body_last = tree.lastToken(body);

    var t: Ast.TokenIndex = body_first;
    while (t <= body_last) : (t += 1) {
        const source_tok = wholeValueCopySourceAt(tags, t, body_last) orelse continue;
        const name = tree.tokenSlice(source_tok);
        const dest = paramHandleType(state.cache, tree, proto, name) orelse continue;
        // The fix for a whole-value copy is an acquire that reaches
        // EVERY field the copy duplicates: `source.ref.retain();` and
        // `source.tail.retain();` before the return balance one second
        // owner each.  Only an acquire WRITTEN BEFORE the copy can
        // balance it, so the scan ends at the copy — one that runs
        // afterwards is a statement the copy can no longer reach.
        const unacquired = unacquiredOwnedRef(
            state.cache,
            proto,
            body,
            tree,
            tags,
            dest,
            body_first,
            source_tok,
            name,
        ) orelse continue;
        try reportWholeCopy(gpa, state.problems, tree, source_tok, name, dest.info.name, unacquired);
    }
}

/// The identifier a whole-value copy at `t` copies, when that copy's
/// source is a bare name.  Two spellings: `return <name>;` and
/// `const|var <dest> [= <name>];` with the source written bare.  A
/// right-hand side with any token after the name — `.field`, `.*`,
/// `(`, `[`, `&` — is a different expression with its own verdict.
fn wholeValueCopySourceAt(
    tags: []const std.zig.Token.Tag,
    t: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    if (tags[t] == .keyword_return) {
        if (t + 2 > last) return null;
        if (tags[t + 1] != .identifier) return null;
        // A switch prong's statement list ends at a COMMA, so a `return`
        // written as the whole of one prong — `else => return source,` —
        // is a copy like any other and is ended by the prong's own comma.
        if (tags[t + 2] != .semicolon and tags[t + 2] != .comma) return null;
        return t + 1;
    }
    if (tags[t] != .keyword_const and tags[t] != .keyword_var) return null;
    if (t + 2 > last or tags[t + 1] != .identifier) return null;
    // Step over an optional `: <type>` annotation to the `=` at depth 0.
    var eq: Ast.TokenIndex = t + 2;
    if (tags[eq] == .colon) {
        var depth: u32 = 0;
        while (eq < last) : (eq += 1) {
            switch (tags[eq]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => {
                    if (depth == 0) return null;
                    depth -= 1;
                },
                .equal => if (depth == 0) break,
                .semicolon => if (depth == 0) return null,
                else => {},
            }
        }
    }
    if (eq + 2 > last) return null;
    if (tags[eq] != .equal) return null;
    if (tags[eq + 1] != .identifier) return null;
    if (tags[eq + 2] != .semicolon) return null;
    return eq + 1;
}

/// The declaration a whole-value copy names, when the name is one of
/// this function's BY-VALUE parameters and its declared type is a
/// value type this file can bind.  Null for an address — a pointer, a
/// slice or an array, whose storage belongs to whoever allocated it and
/// whose copy duplicates no reference count — and for a type
/// expression this file cannot read, which leaves the question open
/// rather than answering it.
fn paramHandleType(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    name: []const u8,
) ?DestType {
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        const name_tok = param.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_tok), name)) continue;
        const type_expr = param.type_expr orelse return null;
        if (spellsAddress(tree, type_expr)) return null;
        return bindTypeExpr(cache, tree, type_expr);
    }
    return null;
}

/// True iff the type expression hands over an ADDRESS rather than a
/// value: `*T`, `**T`, `&T`, `[]T` or `[N]T`.
fn spellsAddress(tree: *const Ast, type_expr: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(type_expr);
    const last = tree.lastToken(type_expr);
    var t = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .asterisk, .asterisk_asterisk, .l_bracket, .ampersand => return true,
            else => {},
        }
    }
    return false;
}

/// Read every field copy one struct literal makes: `.field = recv.field`.
///
/// The DESTINATION DECLARATION is what decides, and it is read for
/// three things and no more — whether it runs a teardown on that field,
/// what that teardown does with it, and whether the field is a pointer
/// it merely borrows.  The field's spelling and whatever lifecycle
/// calls the rest of the file happens to make on the same name are a
/// fallback for a destination this rule cannot bind at all, never a
/// gate on one it can.
fn checkStructInit(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    init: Ast.Node.Index,
    state: *CheckState,
) !void {
    const tags = tree.tokens.items(.tag);
    // A struct-init node's main token is its opening brace; `firstToken`
    // would walk up into the type expression instead.
    const lbrace = tree.nodeMainToken(init);
    const rbrace = matchingBrace(tree, lbrace);

    // One literal constructs one declaration, so bind it at most once.
    var dest: ?DestType = null;
    var dest_bound = false;

    var depth: u32 = 0;
    var t: Ast.TokenIndex = lbrace;
    while (t <= rbrace) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => depth -= 1,
            else => {},
        }
        // Only this literal's own fields; whatever a nested literal
        // contributes belongs to that node.
        if (depth != 1) continue;

        // Pattern: `. dest_field = source_recv . source_field`
        if (t + 5 > rbrace) continue;
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

        // The RHS is a bare `source_recv.source_field`, not a derived
        // value — a method call (`recv.field.method(…)`) or a sub-field
        // (`recv.field.subfield`) keeps its own period at t + 6.
        if (t + 6 <= rbrace and tags[t + 6] == .period) continue;

        const field_tok = t + 1;

        // MOVE: if the SOURCE is reset to empty after the copy, the
        // assignment hands over the one existing reference instead of
        // sharing it.  Scoped to the enclosing fn, where the reset can
        // still belong to this statement sequence.
        const fn_decl = tokens.enclosingFnDecl(tree, field_tok) orelse continue;
        const body = tokens.bodyOf(tree, fn_decl) orelse continue;
        const fn_last = tree.lastToken(fn_decl);
        if (sourceIsClearedAfter(tree, tags, t + 6, @min(t + 100, fn_last), source_recv, source_field)) continue;

        if (!dest_bound) {
            dest = bindDestination(state.cache, tree, init);
            dest_bound = true;
        }

        // The DESTINATION DECLARATION answers this copy, and nothing
        // else does.  What it runs on the field is the only question:
        // neither the spelling of the name nor a lifecycle call some
        // other type in the file happens to make on the same name has
        // any say in it.
        const verdict = verdictOnField(state.cache, dest, dest_field);
        var balances_by_acquire = false;
        switch (verdict) {
            .borrowed => continue,
            .owned => |payload| balances_by_acquire = payload == .protocol,
            // No declaration to read.  What is left is the coarse
            // reading this rule has always had: a name that suggests an
            // owned field, on a spelling the file gives a lifecycle
            // somewhere.  It stays a fallback rather than a gate, so a
            // declaration that CAN be read is never overridden by it.
            .unknown => {
                // Field name must suggest a refcounted / owned type.
                if (!isRefcountedFieldName(dest_field)) continue;
                // Value types (e.g. `Ref = packed struct(u64)`) never
                // appear with `.ref.deinit()` or `.ref.clone()`.
                if (!state.evidenced.contains(dest_field)) continue;
            },
        }

        // An acquire balances the copy only where the declaration
        // drives the field through the field's own reference protocol.
        // A teardown that takes the field's storage apart itself, frees
        // its own receiver, or cannot be read is charged whatever any
        // count says, so a retain written on the field is no fix for it.
        //
        // The acquire is read on the copy's OWN path: from the opening
        // brace of the enclosing body to the token before this field, so
        // a statement written anywhere ahead of the copy balances it and
        // one written after it — or inside another function — does not.
        // Written ahead is not the same as reached: an acquire inside a
        // branch that ends before this field runs does not balance a copy
        // written outside that branch.
        if (balances_by_acquire and
            copyIsAcquired(state.cache, tree, tags, fn_decl, body, field_tok, source_recv, source_field)) continue;

        try report(gpa, state.problems, tree, field_tok, dest_field, source_recv);
    }
}

/// True iff this copy is already balanced by a second reference
/// acquired on its OWN source and field before the copy runs.
///
/// The window is the enclosing function's own body — its `{` up to the
/// token before this field — because that is the only place an acquire
/// can reach the copy: one written after it is a statement the copy can
/// no longer use, and one written in another function never runs on
/// this path at all.  Reading a fixed number of tokens back instead
/// would call a copy balanced when the acquire sits behind whatever
/// statements the body happens to open with, and leave a real fix
/// unread when it sits behind a great many.
///
/// Written ahead of the copy is not the same as reaching it either.  An
/// acquire inside a branch that has closed by the time this field is
/// built ran on the paths that took that branch and on no other, so it
/// leaves the copy unbalanced on every path that skipped it; the same
/// acquire written in the same branch as the copy is the fix for that
/// copy and for no other.
///
/// Two shapes count, and they are the ones the whole-value pass reads:
/// the call written on the source and field themselves, and the same
/// call written through an immutable local bound from exactly those —
/// each matched through the bindings seam, so a local of the same name
/// in a nested block, or one bound from a member of the field, is not
/// this source's reference.
fn copyIsAcquired(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    fn_decl: Ast.Node.Index,
    body: Ast.Node.Index,
    field_tok: Ast.TokenIndex,
    source_recv: []const u8,
    source_field: []const u8,
) bool {
    const body_first = tree.firstToken(body);
    const before_copy = field_tok -| 1;
    if (hasRefAcquireCall(tree, tags, body_first, before_copy, field_tok, source_recv, source_field)) return true;
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return false;
    return hasAliasRefAcquireCall(
        cache,
        proto,
        body,
        tree,
        tags,
        body_first,
        before_copy,
        source_recv,
        source_field,
    );
}

/// Index of the `}` closing the `{` at `lbrace`.
fn matchingBrace(tree: *const Ast, lbrace: Ast.TokenIndex) Ast.TokenIndex {
    var depth: u32 = 0;
    var t = lbrace;
    while (t < tree.tokens.len) : (t += 1) {
        switch (tree.tokenTag(t)) {
            .l_brace => depth += 1,
            .r_brace => {
                depth -= 1;
                if (depth == 0) return t;
            },
            else => {},
        }
    }
    return lbrace;
}

/// Bind the DECLARATION a struct literal constructs: `Owner`,
/// `pkg.Owner`, `Outer.Inner`, or — for an anonymous literal — whatever
/// the context says it constructs.  A pointer or slice type, a
/// contextual type this file cannot read, and any name this rule cannot
/// resolve all yield null, and the caller then keeps its coarse
/// verdict rather than borrowing another declaration's.
fn bindDestination(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    init: Ast.Node.Index,
) ?DestType {
    var buffer: [2]Ast.Node.Index = undefined;
    const literal = tree.fullStructInit(&buffer, init) orelse return null;
    if (literal.ast.type_expr.unwrap()) |type_expr| return bindTypeExpr(cache, tree, type_expr);
    return contextualDestination(cache, tree, init);
}

/// The declaration an ANONYMOUS literal (`.{ … }`) constructs, read
/// from what its own context says the value is: the type the enclosing
/// function returns, or the type an annotated local is declared with.
///
/// The context is the only thing that names it.  Reading the SOURCE's
/// type instead would answer the question the literal was written to
/// ask about the wrong declaration — and would declare a borrowed view
/// an owner whenever the two happened to differ, which is exactly the
/// case worth getting right.  An unannotated local, an assignment to a
/// field or through a pointer, and a literal this rule cannot place in
/// either position all read as nothing.
fn contextualDestination(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    init: Ast.Node.Index,
) ?DestType {
    const tags = tree.tokens.items(.tag);
    const lbrace = tree.nodeMainToken(init);
    // `.{ … }` opens with a period of its own; the token before the
    // brace is that period or the `=` the literal is assigned by.
    if (lbrace == 0) return null;
    var before: Ast.TokenIndex = lbrace - 1;
    while (before > 0 and tags[before] == .period) before -= 1;

    if (tags[before] == .keyword_return) {
        // `return .{ … };` — the whole returned expression.  A literal
        // the return then chains off (`return .{ … }.init()`) constructs
        // something else, so it is not the returned type's to decide.
        const rbrace = matchingBrace(tree, lbrace);
        if (rbrace + 1 >= tree.tokens.len or tags[rbrace + 1] != .semicolon) return null;
        const fn_decl = tokens.enclosingFnDecl(tree, before) orelse return null;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return null;
        const return_type = proto.ast.return_type.unwrap() orelse return null;
        return bindTypeExpr(cache, tree, return_type);
    }

    // `const name : Type = .{ … }` — the annotation names the type the
    // local is declared with, which is the type the literal constructs.
    if (tags[before] != .equal or before == 0) return null;
    const name_last = before - 1;
    if (tags[name_last] != .identifier) return null;
    const colon = annotationColonBefore(tags, name_last) orelse return null;
    return bindTypeRange(cache, tree, colon + 1, name_last);
}

/// The `:` of `const name : Type` where `name_last` is the last token
/// of `Type`, or null when the tokens before it are not that
/// annotation.  The walk stops at anything that ends a statement, so
/// it can never cross one to find a colon belonging to another.
fn annotationColonBefore(
    tags: []const std.zig.Token.Tag,
    name_last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    var t = name_last;
    while (t > 0) : (t -= 1) {
        switch (tags[t]) {
            .colon => {
                if (t < 2) return null;
                if (tags[t - 1] != .identifier) return null;
                if (tags[t - 2] != .keyword_const and tags[t - 2] != .keyword_var) return null;
                return t;
            },
            .identifier, .period, .question_mark, .asterisk, .asterisk_asterisk, .keyword_const => {},
            else => return null,
        }
    }
    return null;
}

/// Bind a type EXPRESSION — a struct literal's type, a parameter's
/// declared type, a return type — to the declaration it names.  A
/// leading `?` is the same handle, unwrapped; a pointer, a slice, an
/// array or a generic instantiation carries no single declaration to
/// bind, as does any name this file cannot read.
fn bindTypeExpr(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    type_expr: Ast.Node.Index,
) ?DestType {
    return bindTypeRange(cache, tree, tree.firstToken(type_expr), tree.lastToken(type_expr));
}

/// The declaration a type written over `[first, last]` names: `Name`,
/// `pkg.Name`, `Outer.Inner.Name`, at whatever depth it is written at.
/// The path is read through the same named-type reader the rest of this
/// codebase resolves a declared type with, so a path deeper than any
/// fixed buffer still names a type this file declares instead of
/// reading as no type at all — and charging a handle whose head type is
/// perfectly well declared.
///
/// The name is written in THIS file, so it is read in THIS file's scope:
/// its imports and its aliases are what the path is written against, and
/// a declaration reached through one answers from the file that declares
/// it.  A qualified path and a bare one therefore reach the same reader
/// — which is what an imported owner and the borrowed view spelled
/// beside it both need.  Reading through imports for a bare name only
/// left `imported.Owner` with no declaration at all, so an owner nobody
/// released in this file was charged on the spelling of its field alone,
/// and a borrowed view beside it was reported for a reference that never
/// existed.
fn bindTypeRange(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?DestType {
    const tags = tree.tokens.items(.tag);
    var head = first;
    while (head <= last and tags[head] == .question_mark) head += 1;
    if (head > last) return null;
    // `Name`, `pkg.Name`, `Outer.Inner.Name`: identifiers joined by
    // periods and nothing else, at whatever depth it is written at.
    // Anything else in the range is a shape with no single declaration
    // behind it — a pointer, a slice, an array, a generic
    // instantiation — and is charged rather than read as one.
    var t = head;
    while (true) {
        if (tags[t] != .identifier) return null;
        if (t == last) break;
        if (tags[t + 1] != .period) return null;
        t += 2;
        if (t > last) return null;
    }
    // The WHOLE path is what a declaration is named by: `Registry.View`
    // is a type nested in `Registry`, and the leaf alone finds nothing for
    // it, so the path is what the model's own qualified reader takes.
    var path: [8][]const u8 = undefined;
    var len: usize = 0;
    var s = head;
    while (true) {
        path[len] = tree.tokenSlice(s);
        len += 1;
        if (s == last) break;
        s += 2;
    }

    const model = cache.fileModel() catch return null;
    // The binding answers for the file being READ: a declaration asked
    // for from another file's scope is that file's question, and the
    // model built here would answer it with whatever the analysed file
    // happens to call the name.
    if (model.tree != tree) return null;
    // A head this file bound to an `@import` names ANOTHER file, so the
    // leaf is that file's declaration and never this one's.  Reading the
    // leaf out of this file's own scope first is what answered
    // `imported.Owner` with a same-named local `Owner` that happens to
    // borrow the pointer it was handed, and said nothing about a copy
    // the imported owner releases.
    if (len > 1 and headIsImportAlias(tree, path[0])) {
        if (cache.importedTypeAcrossImports(path[len - 1])) |resolved| {
            return .{ .tree = resolved.model.tree, .info = resolved.info };
        }
        return null;
    }
    if (model.findQualifiedType(path[0..len])) |info| {
        return .{ .tree = model.tree, .info = info };
    }
    if (len > 1) return null;
    // A name this file does not declare may still come in through an
    // import.  The answer carries the document it was read from, because
    // the fields reached through it belong to THAT file's tree.
    //
    // Only the imports THIS file reaches are read.  The project-wide
    // type index behind `resolvedTypeAcrossImports` answers by name over
    // every file under the project root, so it costs a whole-project
    // directory walk to answer a question asked once per declaration —
    // and it can only answer it wrongly here: a head no import reaches
    // comes back as whatever same-named type some other package declares.
    // A head that is not reachable is charged, which is what it is.
    if (cache.importedTypeAcrossImports(path[0])) |resolved| {
        return .{ .tree = resolved.model.tree, .info = resolved.info };
    }
    return null;
}

/// True iff `name` is bound to an `@import` at the top level of this
/// file: `const imported = @import("shapes.zig");`.
fn headIsImportAlias(tree: *const Ast, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    const last: Ast.TokenIndex = @intCast(tags.len);
    var t: Ast.TokenIndex = 0;
    while (t + 5 < last) : (t += 1) {
        if (tags[t] != .keyword_const) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), name)) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), "@import")) continue;
        return tags[t + 4] == .l_paren;
    }
    return false;
}

/// What `dest` does with `field_name`.  The declared type and the
/// protocol it actually runs on the field are the only two facts read —
/// never the field's spelling, and never another type's teardown.
fn verdictOnField(
    cache: *file_cache_mod.FileCache,
    dest: ?DestType,
    field_name: []const u8,
) FieldVerdict {
    const d = dest orelse return .unknown;
    const field = d.info.findField(field_name) orelse return .unknown;
    if (lifecycleMethodOnField(cache, d.tree, d.info, field_name)) |teardown| {
        // A field handed to a callee as the standard allocator BY
        // VALUE is a capability the callee borrows, not a reference
        // this declaration gives back.
        if (teardown.payload == .borrowed_argument) return .borrowed;
        return .{ .owned = teardown.payload };
    }
    if (declaredPointer(d.tree, field)) return .borrowed;
    return .unknown;
}

/// True iff `dest` is declared as a pointer — `*T`, `?*T`, `*const T`,
/// `?*const T`.  A pointer field is the shape a borrowed view takes: it
/// aliases storage whose lifetime somebody else decides.
fn declaredPointer(tree: *const Ast, field: *const file_model_mod.FieldInfo) bool {
    const tags = tree.tokens.items(.tag);
    var t = field.type_first;
    while (t <= field.type_last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => {},
            .asterisk => return true,
            else => return false,
        }
    }
    return false;
}

/// What a declaration's own teardown does with one of its fields, read
/// from the CALLEE's declaration rather than from the spelling of the
/// call: the same `free`/`destroy` spelling stands for all four of
/// these, and which one it is decides both which side of the call the
/// payload is on and whether an acquire on the field is a fix.
const Payload = enum {
    /// A reference PROTOCOL drives the field — `self.f.deinit(…)`,
    /// `self.f.deref(gpa)`, a value derived from the field driving
    /// `release(…)`.  The field's own count decides when its storage
    /// goes, so acquiring it is what a copy of the handle needs.
    protocol,
    /// The field is HANDED to something that frees it outright —
    /// `self.gpa.destroy(self.f)`, `alloc.dealloc(self.buf)`.  The
    /// handle a handoff is made on is the mechanism, and the field it
    /// is handed is destroyed whatever any count says.
    destroyed_argument,
    /// The field is the value the call is MADE on, and that callee
    /// frees its own receiver's storage — `self.node.free(self.gpa)`.
    /// The allocator handed to that call is a borrowed argument.
    freed_receiver,
    /// The field is HANDED to the callee as an argument the callee
    /// does not prove it destroys, and the field is the standard
    /// allocator BY VALUE — `self.node.free(self.gpa)` into a
    /// `free(self, gpa: std.mem.Allocator)`.  What such a callee
    /// receives is a capability it borrows: a copy of the handle
    /// duplicates no reference, and holding one is not holding a
    /// second owner of anything.
    ///
    /// It is a verdict about the ARGUMENT side alone, and it is the
    /// callee's own declaration that decides it: no field name, no
    /// argument position and no proof about the OTHER side of the
    /// call stands in for it.  A POINTER to the allocator is not this
    /// value — the descriptor it points at is heap storage somebody
    /// owns — so one stays `.unknown`, charged with everything else
    /// this rule cannot read.
    borrowed_argument,
    /// Whichever side the callee frees cannot be read here: the head's
    /// declared type does not resolve, the callee is not declared by
    /// it, the import behind it is not reachable — or the callee IS
    /// readable and its body proves neither side, because it forwards
    /// the teardown, frees its receiver through a pointer this rule
    /// cannot follow, or is declared here without a body.  NEITHER side
    /// is called quiet, and no acquire is taken as proof of a protocol
    /// this rule has not seen.
    unknown,
};

/// The tokens a declared type is written in, as one inclusive range of
/// the snapshot that declares it.
const TypeRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// The method a declaration hands `field_name` back through, and what
/// it does with it.  A copy reports the method; the payload decides
/// whether the copy can be balanced by an acquire.
const Teardown = struct {
    method: []const u8,
    payload: Payload,
};

/// The teardown a method of `ti` performs on `field_name`, or null when
/// no method does.  It is the ENCLOSING method, not the refcount call
/// its body makes on the pointee: `Shared.drop` releasing `tail`
/// through `tail.deref(gpa)` is reported as `drop`, because `drop` is
/// the method a reader has to open to see who gives the reference back.
///
/// Only methods WITH a receiver are read.  A static
/// `fn free(ctx: *anyopaque, bytes: []u8)` is an allocator interface
/// callback: the buffer it frees belongs to whoever allocated it, so it
/// is nobody's destructor and hands this field back to nobody.
fn lifecycleMethodOnField(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    ti: *const file_model_mod.TypeInfo,
    field_name: []const u8,
) ?Teardown {
    for (ti.methods) |*m| {
        const receiver = m.receiver orelse continue;
        const payload = methodReachesField(cache, tree, ti, m, receiver.name, field_name) orelse continue;
        return .{ .method = m.name, .payload = payload };
    }
    return null;
}

/// What this method's body does with `recv.field_name`, or null when
/// its body hands that field back to nobody.  Four shapes count, each
/// read as exactly that shape and nothing wider:
///
///   * the field is the RECEIVER of a reference protocol call —
///     `self.f.release(…)`, or the same through the optional unwrap,
///     `self.f.?.release(…)`.  `.?` tokenizes as `.period` then
///     `.question_mark`, so the call name sits past the period that
///     follows the field and the question mark, not where a two-token
///     reading would put it.  A storage handoff is NOT read here: what
///     a `free`/`destroy`/`dealloc`/`delete` call hands back is the
///     callee's to say, and the pass below reads it there.
///   * the field is the payload of a storage handoff — written as its
///     argument, `self.gpa.destroy(self.f)`, or as the value the call
///     is made on, `self.node.free(self.gpa)` — decided by the callee,
///     never by which side of the call the field was written on.
///   * a name bound from the field drives the protocol — `const snap =
///     self.f`, `const snap = self.f.?`, then `snap.release(…)`.
///   * a single-item capture whose SCRUTINEE is exactly `recv.field`,
///     optionally unwrapped — `if (self.f) |snap| snap.release(…)`.
///     The capture's own parentheses are read for the scrutinee, so a
///     capture of anything else — `if (self.gpa) |err|`, `while
///     (it.next()) |item|` — binds a name that is not this field's and
///     is never credited here.
///
/// Every derived name is followed the moment it is found and read
/// against the binding its own protocol call names, so how many a body
/// may bind is not a question this reader has an answer to.
fn methodReachesField(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    ti: *const file_model_mod.TypeInfo,
    m: *const file_model_mod.MethodInfo,
    recv: []const u8,
    field_name: []const u8,
) ?Payload {
    const first = m.body_first;
    const last = m.body_last;
    const tags = tree.tokens.items(.tag);
    if (!namesField(tree, tags, first, last, recv, field_name)) return null;

    var t = first;
    while (t + 6 <= last) : (t += 1) {
        if (!isRecvFieldAt(tree, tags, t, last, recv, field_name)) continue;
        // `self.f.release(…)` — the field is the receiver.
        if (tags[t + 3] == .period and tags[t + 5] == .l_paren and
            isLifecycleMethod(tree.tokenSlice(t + 4)) and
            !isStorageHandoffName(tree.tokenSlice(t + 4))) return .protocol;
        // `self.f.?.release(…)` — `.` `?` `.` `release` `(`
        if (tags[t + 3] == .period and tags[t + 4] == .question_mark and
            tags[t + 5] == .period and tags[t + 6] == .identifier and
            t + 7 <= last and tags[t + 7] == .l_paren and
            isLifecycleMethod(tree.tokenSlice(t + 6)) and
            !isStorageHandoffName(tree.tokenSlice(t + 6))) return .protocol;
    }

    // A storage handoff hands something back, and WHICH side of the
    // call carries it is the callee's own declaration:
    //
    //   self.gpa.destroy(self.f)  — the payload is the ARGUMENT: `gpa`
    //                                is only the mechanism that frees
    //                                it.
    //   self.gpa.?.destroy(self.f) — the same call through an optional
    //                                head, `.` `?` `.` `destroy` `(`.
    //   self.node.free(self.gpa)   — the payload is the HEAD: `Node.free`
    //                                frees its own receiver, and the
    //                                allocator handed to it is a
    //                                borrowed argument.
    // A callee this rule cannot read leaves BOTH sides charged, and so
    // does one it can read and still cannot follow to a verdict — a
    // teardown forwarded to another method, a receiver freed through a
    // function pointer.  An imported or forwarded owning pointer is
    // never declared borrowed by a guess about which half the call
    // frees.
    var h = first;
    while (h + 5 <= last) : (h += 1) {
        if (tags[h] != .identifier) continue;
        if (tags[h + 1] != .period) continue;
        var call = h + 2;
        if (tags[call] == .question_mark) {
            if (tags[call + 1] != .period) continue;
            call += 2;
        }
        if (tags[call] != .identifier) continue;
        if (!isStorageHandoffName(tree.tokenSlice(call))) continue;
        if (tags[call + 1] != .l_paren) continue;
        const close = tokens.matchParen(tags, call + 1, last) orelse continue;
        const payload = handoffPayload(cache, tree, ti, m, h, call, close, recv, field_name);
        // `self.gpa.destroy(self.f)` — the field is handed to a
        // sibling's storage handoff instead of being called on.  A
        // head that frees its own storage does not take one, an
        // unreadable one may, and an allocator value the callee
        // borrows is not this declaration's to give back either.
        if (payload != .freed_receiver and payload != .borrowed_argument and
            fieldPassedAt(tree, tags, call + 2, close -| 1, recv, field_name)) return payload;
        // `self.node.free(self.gpa)` — the field the call is MADE on is
        // what this teardown gives back, unwrapped or not.
        if (payload != .destroyed_argument and h >= 2 and tags[h - 1] == .period and
            isRecvFieldAt(tree, tags, h - 2, last, recv, field_name)) return payload;
    }

    // Names the body takes FROM the field and then drives a refcount
    // through.  Each one is matched to the field it was bound from and
    // to the binding the protocol call names, so a name that merely
    // appears in the same body — the allocator an `if (self.data) |d|
    // d.release(self.gpa)` passes as an argument, a name bound from
    // some other expression, a same-spelled capture of some other value
    // in a nested scope — is not one of them.  Nothing is accumulated
    // here, so a ninth, a nineteenth or a ninety-ninth binding is read
    // with the same care as the first.
    var k = first;
    while (k <= last) : (k += 1) {
        if (tags[k] != .identifier) continue;
        // `const snap = self.f` / `var snap = self.f.?` — `k` is the NAME
        // the body binds, so `=` stands after it and the field starts two
        // tokens further on; reading the `=` behind the name instead asks
        // about the name itself, and no `const x = self.f` binding was
        // ever matched.
        if (k >= first + 1 and tags[k + 1] == .equal and
            (tags[k - 1] == .keyword_const or tags[k - 1] == .keyword_var) and
            isRecvFieldAt(tree, tags, k + 2, last, recv, field_name) and
            rhsIsTheField(tags, k + 5, last))
        {
            if (drivesProtocol(cache, tree, m, tags, last, tree.tokenSlice(k), k)) return .protocol;
            continue;
        }
        // `if (self.f) |snap|` — the pipe closes the capture list.
        if (k >= first + 1 and tags[k - 1] == .pipe) {
            if (captureNameFromField(tree, tags, first, last, k - 1, recv, field_name)) |name| {
                if (std.mem.eql(u8, name, tree.tokenSlice(k)) and
                    drivesProtocol(cache, tree, m, tags, last, name, k)) return .protocol;
            }
            continue;
        }
        // `while (self.f) |*snap|` — a pointer capture binds the same
        // one name, one token further from the pipe.
        if (k >= first + 2 and tags[k - 1] == .asterisk and tags[k - 2] == .pipe) {
            if (captureNameFromField(tree, tags, first, last, k - 2, recv, field_name)) |name| {
                if (std.mem.eql(u8, name, tree.tokenSlice(k)) and
                    drivesProtocol(cache, tree, m, tags, last, name, k)) return .protocol;
            }
        }
    }
    return null;
}

/// What the callee of the storage handoff written `<head> . <handoff> ( … )`
/// does with the value the field under consideration is written on.  It
/// is the callee's own declaration — never the name of the method, the
/// name of the field it hangs off, or a prefix the field's spelling
/// happens to share:
///
///   * `self.gpa.destroy(self.name)` — the head's declared type is read
///     as the standard allocator, through the scopes that type is written
///     in (`std.mem.Allocator`, `mem.Allocator`, an alias of either) and
///     through a POINTER to it, so its own deallocation contract frees
///     the ARGUMENT either way.  `name` is the reference this type owns;
///     `gpa` is the mechanism that frees it, and copying a `gpa`-holding
///     handle duplicates no reference to it.  A head is never charged
///     by that type name, though: a `destroy` made through
///     `*std.mem.Allocator` frees what it is HANDED and leaves the
///     descriptor it points at allocated, so the descriptor is settled
///     by the handoff that really takes it apart, and not by the fact
///     that a pointer at it exists.
///   * `self.node.free(self.gpa)` — the head's declared type resolves,
///     so `Node.free`'s own body decides: it frees `self.text`, so the
///     payload is the head.  `node` is what the teardown owns and the
///     allocator handed to it is a borrowed argument.
///   * `self.registry.destroy(self.name)` — the callee's own body hands
///     the parameter it is PASSED to something that destroys storage, so
///     the argument is what this teardown gives back.  The call's
///     argument position is matched against the callee's parameters,
///     because a body that only forwards its argument
///     (`self.finish(entry)`) proves nothing about it.
///   * a field PASSED as an argument the callee does not prove it
///     destroys — `self.node.free(self.gpa, self.other_ref)` — is
///     answered on its own proofs only.  What the callee's body shows
///     about its RECEIVER is a different field's evidence and settles
///     nothing here: `Node.free` freeing `self.bytes` says nothing
///     about the `other_ref` it forwards to `finishOther`, and reading
///     it as though it did is what declared a forwarded owning pointer
///     borrowed.  Such an argument is charged, unless the field is the
///     allocator by value — `.borrowed_argument`, a capability the
///     callee borrows, which no field name, argument position or
///     allocator-argument exemption can stand in for.  A field written
///     on BOTH sides of one call is charged too: no single verdict
///     covers it.
///   * a callee this rule cannot read — an allocator behind an alias it
///     cannot follow, a type reached through an import it does not
///     resolve, a type that declares no such method — is `.unknown`,
///     and an unknown charges BOTH sides.  So is a callee this rule CAN
///     open but whose body proves neither side: a teardown forwarded to
///     another method, a receiver freed through a function pointer, a
///     method declared here without a body.  An absence of a direct
///     free is not a proof that the ARGUMENT is the payload, and reading
///     it as one is what declared a forwarded or imported owning pointer
///     borrowed and named the copied allocator the reference it
///     duplicates.
///
/// `head` is the value the call is made ON and `call` the token its
/// handoff name is written at — the same token for `head . free ( … )`
/// and for `head . ? . free ( … )`.  `close` is the `)` that ends the
/// call, and `field_name` the field the verdict is wanted FOR: one
/// call charges two sides at once, and which of them this field is
/// decides what the callee has to prove about it.
fn handoffPayload(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    ti: *const file_model_mod.TypeInfo,
    m: *const file_model_mod.MethodInfo,
    head: Ast.TokenIndex,
    call: Ast.TokenIndex,
    close: Ast.TokenIndex,
    recv: []const u8,
    field_name: []const u8,
) Payload {
    const tags = tree.tokens.items(.tag);
    const handoff = tree.tokenSlice(call);
    const declared = headTypeRange(tree, ti, m, head, recv) orelse return .unknown;
    // The library's own source is not in this session's reach, so the
    // allocator is read the way it is WRITTEN: through the scopes the
    // name is bound in, whatever wrappers the declaration puts in
    // front of it.  A POINTER to it answers the same way the value
    // does, because that is what the standard API is: `raw_gpa.destroy(x)`
    // auto-derefs to the very same `Allocator` interface and frees `x`.
    // What such a head never does is take apart the descriptor it points
    // at, so nothing here charges the head itself — the ARGUMENT is the
    // payload, and the descriptor stays charged wherever a real handoff
    // of it is written.
    if (std_type_query.isType(cache, tree, declared.first, declared.last, "mem", "Allocator", .{
        .allow_pointer = true,
    })) return .destroyed_argument;
    // `self.node.free(self.gpa)` — the field is the value the call is
    // MADE on, and only the callee's own receiver says what such a
    // field gives back.
    const on_head = head >= 2 and tags[head - 1] == .period and
        isRecvFieldAt(tree, tags, head - 2, m.body_last, recv, field_name);
    const passed_at = argumentPositionOfField(tree, tags, call + 2, close -| 1, recv, field_name);
    // One field on both sides of one call is a field no single
    // verdict covers, so nothing is called quiet for it.
    if (passed_at != null and on_head) return .unknown;
    // What a callee is HANDED the standard allocator BY VALUE is a
    // capability it borrows, and that is the callee's own business: it
    // was handed one whatever this rule can read about the callee
    // behind it, and holding a copy of it duplicates no reference.  So
    // this is settled before the callee is opened — a callee this rule
    // cannot resolve has still been handed one, and charging it is what
    // named the copied allocator the reference the copy duplicates.
    if (passed_at != null and isBorrowedAllocatorValue(cache, tree, ti, field_name))
        return .borrowed_argument;
    const owner = declaredTypeDeclAt(cache, tree, declared.first, declared.last) orelse return .unknown;
    const method = owner.info.findMethod(handoff) orelse return .unknown;
    if (passed_at) |position| {
        // `self.registry.destroy(self.name)` — a callee that PROVES it
        // destroys what it is PASSED: `Registry.destroy` handing
        // `entry` to its own allocator.  The position is counted in
        // the call's own argument list and matched against the
        // callee's parameters, so a field passed at some other
        // position is never read as this one's.
        if (methodDestroysParameterAt(cache, owner.tree, method, position)) return .destroyed_argument;
        // This argument is NOT proved destroyed, and that is where the
        // reading of THIS side ends.  The callee's receiver is
        // evidence about the head and settles nothing about a field
        // written as an argument: `Node.free` freeing `self.bytes`
        // says nothing about the `other` it forwards to `finishOther`,
        // and letting it say so is what declared a forwarded owning
        // pointer borrowed.  So the argument stays charged.
        return .unknown;
    }
    // A callee that hands its OWN receiver's storage back gives the
    // head back.  A field written as an argument is not settled by it —
    // that question was answered above, on its own proofs — so the
    // verdict here is about the head and about nothing else.
    if (methodFreesItsReceiver(owner.tree, method)) return .freed_receiver;
    return .unknown;
}

/// The tokens the value a call is made ON is declared with, when this
/// method declares it: a field of this value (`self.gpa`), or one of
/// this method's own parameters (`gpa`).  A member of some other value,
/// a local, or any other expression reads as nothing, which leaves the
/// caller charging both sides of the call rather than choosing one.
fn headTypeRange(
    tree: *const Ast,
    ti: *const file_model_mod.TypeInfo,
    m: *const file_model_mod.MethodInfo,
    head: Ast.TokenIndex,
    recv: []const u8,
) ?TypeRange {
    const tags = tree.tokens.items(.tag);
    const head_name = tree.tokenSlice(head);
    // `self . field . handoff ( … )` — the call is made on a field.
    if (head >= 2 and tags[head - 1] == .period and tags[head - 2] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(head - 2), recv))
    {
        const field = ti.findField(head_name) orelse return null;
        return .{ .first = field.type_first, .last = field.type_last };
    }
    // A member of some other value is not this method's to resolve.
    if (head != 0 and tags[head - 1] == .period) return null;
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, m.fn_decl) orelse return null;
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        const name_tok = param.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_tok), head_name)) continue;
        const type_expr = param.type_expr orelse return null;
        return .{ .first = tree.firstToken(type_expr), .last = tree.lastToken(type_expr) };
    }
    return null;
}

/// True iff `ti` declares `field_name` as the standard allocator BY
/// VALUE — `std.mem.Allocator`, `mem.Allocator`, an alias of either,
/// read through the scopes that name is bound in.  What a callee is
/// HANDED such a field borrows: the handle is copied, its storage is
/// not duplicated, and the field is not a reference this declaration
/// ever gives back.
///
/// The answer is the field's own DECLARED TYPE and nothing else.  A
/// pointer to the allocator is not this value — `*std.mem.Allocator`
/// and `?*const std.mem.Allocator` point at a descriptor somebody
/// allocated, which the callee may or may not own — so a pointer, a
/// type reached through an import this file cannot follow and a field
/// that resolves to nothing all answer false and stay charged.
fn isBorrowedAllocatorValue(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    ti: *const file_model_mod.TypeInfo,
    field_name: []const u8,
) bool {
    const field = ti.findField(field_name) orelse return false;
    return std_type_query.isType(cache, tree, field.type_first, field.type_last, "mem", "Allocator", .{
        .allow_pointer = false,
    });
}

/// True iff `m` hands its OWN receiver's storage back to an allocator:
/// `gpa.free(self.text)`, `alloc.dealloc(self.buffer)`.  A method that
/// hands some other value back — `self.rawFree(ptr, …)` — frees its
/// argument, and the receiver of that method is only the mechanism.
fn methodFreesItsReceiver(
    tree: *const Ast,
    m: *const file_model_mod.MethodInfo,
) bool {
    const receiver = m.receiver orelse return false;
    const tags = tree.tokens.items(.tag);
    var t = m.body_first;
    while (t + 3 <= m.body_last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!isStorageHandoffName(tree.tokenSlice(t + 2))) continue;
        if (tags[t + 3] != .l_paren) continue;
        const close = tokens.matchParen(tags, t + 3, m.body_last) orelse continue;
        if (namesReceiverAt(tree, tags, t + 4, close -| 1, receiver.name)) return true;
    }
    return false;
}

/// The position, counted from zero, at which `recv . field_name` is
/// passed as an argument of a call whose arguments run in
/// `[start, end]` — null when it is not one of them.  Only commas at
/// the top level of the list separate arguments, so
/// `registry.destroy(self.gpa.alloc(), self.name)` counts two and the
/// field lands on the second.
fn argumentPositionOfField(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field_name: []const u8,
) ?usize {
    if (start > end) return null;
    var position: usize = 0;
    var argument_first = start;
    var depth: u32 = 0;
    var t = start;
    while (t <= end) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => depth -|= 1,
            .comma => {
                if (depth != 0) continue;
                if (fieldPassedAt(tree, tags, argument_first, t -| 1, recv, field_name)) return position;
                position += 1;
                argument_first = t + 1;
            },
            else => {},
        }
    }
    if (fieldPassedAt(tree, tags, argument_first, end, recv, field_name)) return position;
    return null;
}

/// True iff `m`'s OWN body hands the parameter at `position` back to
/// something that destroys storage — `gpa.destroy(entry)`,
/// `alloc.free(bytes)` — where position zero is the FIRST PARAMETER
/// AFTER THE RECEIVER, the index the caller's first argument lands on.
/// The name is read from the callee's own prototype and matched at the
/// use through the binding seam, so a local of the same name in a
/// nested block is not this parameter, and a parameter the callee only
/// forwards (`self.finish(entry)`) hands nothing back.
///
/// A callee whose bindings this file cannot build — one reached through
/// an import — proves nothing here: its body is read for what it shows,
/// never for what it is bound to.
fn methodDestroysParameterAt(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    m: *const file_model_mod.MethodInfo,
    position: usize,
) bool {
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, m.fn_decl) orelse return false;
    var remaining = position;
    if (m.receiver != null) remaining += 1;
    var parameter_token: ?Ast.TokenIndex = null;
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        if (remaining == 0) {
            parameter_token = param.name_token;
            break;
        }
        remaining -= 1;
    }
    const param_tok = parameter_token orelse return false;
    const bindings = methodBindings(cache, tree, m) orelse return false;
    const name = tree.tokenSlice(param_tok);
    const tags = tree.tokens.items(.tag);
    var t = m.body_first;
    while (t + 3 <= m.body_last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!isStorageHandoffName(tree.tokenSlice(t + 2))) continue;
        if (tags[t + 3] != .l_paren) continue;
        const close = tokens.matchParen(tags, t + 3, m.body_last) orelse continue;
        if (namesParameterAt(tree, tags, bindings, t + 4, close -| 1, name, param_tok)) return true;
    }
    return false;
}

/// True iff `name`, used inside `[start, end]`, still means the
/// PARAMETER declared at `param_token`.  A local of the same name in a
/// nested block would be a different value, and the binding a use names
/// is what tells the two apart.
fn namesParameterAt(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
    param_token: Ast.TokenIndex,
) bool {
    if (start > end) return false;
    var t = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        const used = bindings.findAt(name, t) orelse return false;
        if (used.name_token != param_token) return false;
        return true;
    }
    return false;
}

/// The declaration a TYPE EXPRESSION names over the token range
/// `[first, last]`.  Whatever else the spelling wraps it in — `Name`,
/// `*Name`, `?*const Name`, `pkg.Name`, `Outer.Inner.Name` — the name
/// is the dotted path as the source writes it, at whatever depth it is
/// written at: a reader that could only count to a fixed depth would
/// read a longer path as no type at all, and charge a handle whose head
/// type is perfectly well declared.  The name goes to the seam that
/// answers for a name written in THIS file, which resolves a dotted
/// import and a bare name alike, and which reads a head only through
/// the imports the file reaches — see `bindTypeRange` for why.
fn declaredTypeDeclAt(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?DestType {
    const model = cache.fileModel() catch return null;
    // A declaration reached through an import is written in THAT file's
    // scope: its names are that file's, and a name asked for from here
    // would answer with whatever the analysed file happens to call it.
    if (model.tree != tree) return null;
    const name = declaredTypeName(tree, first, last) orelse return null;
    // `const Alias = Node;` names the very declaration `Node` does, and
    // the model indexes struct/union/enum/opaque declarations only — an
    // alias is not one of them, so a head written through one resolved
    // to nothing and the callee behind it was never opened.  The alias is
    // followed from its own initializer, as many steps as it is written
    // and no further.
    if (resolveLocalType(model, tree, name, 0)) |info| {
        return .{ .tree = model.tree, .info = info };
    }
    const resolved = cache.importedTypeAcrossImports(name) orelse return null;
    return .{ .tree = resolved.model.tree, .info = resolved.info };
}

/// The declaration `name` names in THIS file, following a chain of
/// top-level type aliases to whatever declaration the last one is
/// written as.  An alias declared inside a body is not followed: this
/// walk has no scope to read it in, and a name it cannot place is
/// charged rather than guessed at.
fn resolveLocalType(
    model: *const file_model_mod.FileModel,
    tree: *const Ast,
    name: []const u8,
    depth: u8,
) ?*const file_model_mod.TypeInfo {
    if (depth >= 8) return null;
    if (model.findType(name)) |info| return info;
    const target = aliasTargetName(tree, name) orelse return null;
    return resolveLocalType(model, tree, target, depth + 1);
}

/// The type a file-level `const <name> = <Type>;` is bound to, when that
/// initializer is a bare declaration name.  Anything else — a struct
/// literal, a call, a qualified path — names no single declaration and
/// answers null.
fn aliasTargetName(tree: *const Ast, name: []const u8) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    const last: Ast.TokenIndex = @intCast(tags.len);
    var t: Ast.TokenIndex = 0;
    while (t + 4 < last) : (t += 1) {
        if (tags[t] != .keyword_const) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), name)) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .identifier) continue;
        if (tags[t + 4] != .semicolon) continue;
        return tree.tokenSlice(t + 3);
    }
    return null;
}

/// True iff an initializer that ends at `after` bound the field itself
/// and nothing past it.  `const s = self.f.ref` binds a member of the
/// field, which is a different resource from the one the field holds.
fn rhsIsTheField(tags: []const std.zig.Token.Tag, after: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (after > last) return true;
    if (tags[after] == .semicolon or tags[after] == .comma) return true;
    return after + 1 <= last and
        tags[after] == .period and tags[after + 1] == .question_mark;
}

/// The single name the capture opening at `pipe` binds, when that
/// capture's scrutinee is EXACTLY `recv . field_name` (optionally
/// unwrapped) and the clause binds exactly one name.  A capture of a
/// call result, of a sibling field, or a multi-item clause binds names
/// this field does not own, and returns null for all three.
fn captureNameFromField(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    pipe: Ast.TokenIndex,
    recv: []const u8,
    field_name: []const u8,
) ?[]const u8 {
    if (pipe < first or pipe == 0) return null;
    // `… ( <scrutinee> ) |name|`
    if (tags[pipe - 1] != .r_paren) return null;
    const open = openingParenOf(tags, pipe - 1) orelse return null;
    const scrutinee_first = open + 1;
    const scrutinee_last = pipe - 2;
    if (scrutinee_first > scrutinee_last) return null;
    if (!isRecvFieldAt(tree, tags, scrutinee_first, last, recv, field_name)) return null;
    const is_field = scrutinee_last == scrutinee_first + 2;
    const is_unwrapped = scrutinee_last == scrutinee_first + 4 and
        tags[scrutinee_first + 3] == .period and
        tags[scrutinee_first + 4] == .question_mark;
    if (!is_field and !is_unwrapped) return null;

    const close = closingPipe(tags, pipe + 1, last) orelse return null;
    const item_first = pipe + 1;
    const item_last = close - 1;
    if (item_last < item_first) return null;
    var c = item_first;
    while (c < item_last) : (c += 1) {
        if (tags[c] == .comma) return null;
    }
    const name_first = if (tags[item_first] == .asterisk) item_first + 1 else item_first;
    if (name_first != item_last) return null;
    if (tags[name_first] != .identifier) return null;
    return tree.tokenSlice(name_first);
}

/// True iff the name bound at `name_token` drives the reference
/// protocol — `name . <acquire_or_release> (` — and, where this file
/// can say so, the name at that call still means THAT binding.
///
/// The seam answers that second half per use, which is what keeps a
/// same-spelled binding in a nested scope from being read as this
/// one's protocol: `if (self.f) |held| { if (other) |held| { held.
/// release(…); } }` releases the inner capture of `other`, and the
/// outer one never had a protocol call of its own.  A derived name
/// called from a block it merely reaches through — `const r =
/// self.f;` then `if (c) r.release(…);` — keeps it, because that is
/// the binding the call names.
fn drivesProtocol(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    m: *const file_model_mod.MethodInfo,
    tags: []const std.zig.Token.Tag,
    last: Ast.TokenIndex,
    name: []const u8,
    name_token: Ast.TokenIndex,
) bool {
    const bindings = methodBindings(cache, tree, m);
    var t = name_token;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (!isLifecycleMethod(tree.tokenSlice(t + 2))) continue;
        if (bindings) |b| {
            const used = b.findAt(name, t) orelse continue;
            if (used.name_token != name_token) continue;
        }
        return true;
    }
    return false;
}

/// The memoized bindings of one method body, or null when this rule
/// cannot read them.  The seam is built from the ANALYSED file, so a
/// method of a declaration reached through an import has none here:
/// that body keeps the name-only reading this rule has always had for
/// it, which charges the field rather than losing a teardown.
fn methodBindings(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    m: *const file_model_mod.MethodInfo,
) ?*const local_bindings.LocalBindings {
    const model = cache.fileModel() catch return null;
    if (model.tree != tree) return null;
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, m.fn_decl) orelse return null;
    return cache.localBindings(proto, m.body) catch null;
}

/// The declaration a type expression names: the LAST identifier of the
/// dotted path over `[first, last]`, with leading `?` / `*` / `const` /
/// `volatile` qualifiers stripped.  `Name`, `*Name`, `?*const Name` and
/// `ns.Name` all answer with `Name` — the spelling `FileModel.findType`
/// and `findTypeAcrossImports` resolve — while a slice, an array, a
/// call or anything else in the range names no single declaration and
/// is declined.
fn declaredTypeName(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) ?[]const u8 {
    if (first > last) return null;
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .asterisk, .asterisk_asterisk, .keyword_const, .keyword_volatile, .keyword_allowzero => {},
            .identifier => break,
            else => return null,
        }
    }
    if (t > last) return null;
    var leaf: Ast.TokenIndex = t;
    t += 1;
    while (t <= last) {
        if (tags[t] != .period) return null;
        t += 1;
        if (t > last or tags[t] != .identifier) return null;
        leaf = t;
        t += 1;
    }
    return tree.tokenSlice(leaf);
}

/// The `(` that opens the group the `)` at `close` closes.
fn openingParenOf(tags: []const std.zig.Token.Tag, close: Ast.TokenIndex) ?Ast.TokenIndex {
    var depth: u32 = 0;
    var t = close;
    while (true) {
        switch (tags[t]) {
            .r_paren => depth += 1,
            .l_paren => {
                depth -= 1;
                if (depth == 0) return t;
            },
            else => {},
        }
        if (t == 0) return null;
        t -= 1;
    }
}

/// The `|` that closes a capture list opened before `from`, or null when
/// the list is not closed inside the range read.
fn closingPipe(tags: []const std.zig.Token.Tag, from: Ast.TokenIndex, last: Ast.TokenIndex) ?Ast.TokenIndex {
    var t = from;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .pipe => return t,
            .semicolon, .r_brace => return null,
            else => {},
        }
    }
    return null;
}

/// True iff `recv . field_name` is passed inside `[start, end]`.
fn fieldPassedAt(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field_name: []const u8,
) bool {
    if (start > end) return false;
    var t = start;
    while (t + 2 <= end) : (t += 1) {
        if (isRecvFieldAt(tree, tags, t, end, recv, field_name)) return true;
    }
    return false;
}

/// Names that hand STORAGE back rather than count a reference.  Called
/// on some other value with a field of this type as the argument, they
/// are this type's own teardown of that field.
fn isStorageHandoffName(name: []const u8) bool {
    return std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "dealloc") or
        std.mem.eql(u8, name, "delete");
}

/// True iff `recv . field_name` is spelled at `t`.
fn isRecvFieldAt(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    t: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
    field_name: []const u8,
) bool {
    if (t + 2 > last) return false;
    if (tags[t] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) return false;
    if (tags[t + 1] != .period) return false;
    if (tags[t + 2] != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(t + 2), field_name);
}

/// True iff `recv . field_name` is spelled anywhere in `[first, last]`.
fn namesField(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
    field_name: []const u8,
) bool {
    var t = first;
    while (t + 2 <= last) : (t += 1) {
        if (isRecvFieldAt(tree, tags, t, last, recv, field_name)) return true;
    }
    return false;
}

/// True iff `name` acquires or releases a reference.
///
/// `free` is in the coarse vocabulary but not here: it is one of the
/// words a field really does get a lifecycle from — `self.node.free(gpa)`
/// hands that node back — while a call made on a value DERIVED from a
/// field frees storage rather than counting anything, and reading that
/// as a protocol is what would tell a reader that retaining the field
/// is a fix.
fn isLifecycleMethod(name: []const u8) bool {
    if (std.mem.eql(u8, name, "free")) return false;
    return method_names.isRefAcquireName(name) or isRefReleaseName(name);
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
///
/// `free` belongs here because it is the word this rule reads a
/// hand-back through: a file that only ever spells its teardown that
/// way evidences the fields it runs them on, and a reader that dropped
/// the spelling would miss every one of them.
fn isRefReleaseName(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "deref") or
        std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "unref") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "drop") or
        std.mem.eql(u8, name, "free");
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

/// True iff `[start, end]` holds an actual acquire CALL on
/// `source_recv . source_field`:
///
///   source . field . <acquire> (        (direct)
///   source . field . ? . <acquire> (    (optional unwrap)
///
/// Four facts decide it, and each one is a shape that reads like a
/// balancing acquire without being one:
///
///   * the receiver is the ROOT of the chain.  `wrapper.source.ref` is a
///     member of `wrapper` that happens to be spelled `source`, not the
///     parameter whose reference this copy duplicates.
///   * the acquire name is CALLED.  A method taken as a value —
///     `const dup = source.ref.clone;` — acquires nothing, and a member
///     of the field spelled like an acquire method
///     (`source.handle.ref.retain()`) acquires that member, not the field
///     the copy hands to a second owner.  Both spellings end at the
///     acquire name, and neither is followed by `(`.
///   * the optional unwrap is the same reference.  `source.ref.?.retain()`
///     is how the fix for a `?*T` field is written, exactly as
///     `self.f.?.release(…)` is read on the declaration side.
///   * it is not written inside a `defer` / `errdefer` STATEMENT.  A
///     deferred acquire runs when the scope exits — after the copy it
///     was supposed to balance, and only if the branch inside it is
///     taken at all.
///
///   * it REACHES the copy.  The window above is the whole body, so an
///     acquire written inside the `if`, the `else`, a loop, a `switch`
///     prong or a `catch` payload that closes before the copy is an
///     acquire on the paths that took that branch and on no other — and
///     the copy runs on those other paths too.
fn hasRefAcquireCall(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    copy_tok: Ast.TokenIndex,
    source_recv: []const u8,
    source_field: []const u8,
) bool {
    if (start > end) return false;
    // The shortest shape is `recv . field . method (`.
    if (end < start + 4) return false;
    var frames: ReachFrames = .{};
    // The window the extents are read over ends at the COPY, not one token
    // short of it: a branch the window cuts off is still open around the
    // copy, and a branch that closed before it would have its `}` in the
    // window to close.
    collectReachFrames(tags, start, copy_tok, &frames);
    var t: Ast.TokenIndex = start;
    while (t + 4 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), source_recv)) continue;
        if (t != 0 and tags[t - 1] == .period) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), source_field)) continue;
        if (tags[t + 3] != .period) continue;
        // `source . field . <acquire> (`
        if (tags[t + 4] == .identifier) {
            if (!method_names.isRefAcquireName(tree.tokenSlice(t + 4))) continue;
            if (t + 5 > end) continue;
            if (tags[t + 5] != .l_paren) continue;
            if (deferredCall(tree, t)) continue;
            if (!reachesCopy(&frames, t, copy_tok)) continue;
            return true;
        }
        // `source . field . ? . <acquire> (`
        if (tags[t + 4] == .question_mark) {
            if (t + 7 > end) continue;
            if (tags[t + 5] != .period) continue;
            if (tags[t + 6] != .identifier) continue;
            if (!method_names.isRefAcquireName(tree.tokenSlice(t + 6))) continue;
            if (tags[t + 7] != .l_paren) continue;
            if (deferredCall(tree, t)) continue;
            if (!reachesCopy(&frames, t, copy_tok)) continue;
            return true;
        }
    }
    return false;
}

/// True iff the call whose receiver starts at `call` sits inside a
/// `defer` / `errdefer` statement, whatever that statement wraps.
/// Whatever the `defer` is written directly over — a block, an `if` with
/// a condition of its own, another `defer` — its own extent decides,
/// so `defer source.ref.retain();` and `defer if (cond)
/// source.ref.retain();` are one verdict and neither is decided by the
/// token that happens to precede the receiver.
fn deferredCall(tree: *const Ast, call: Ast.TokenIndex) bool {
    if (tree.tokens.len == 0 or call == 0) return false;
    const tags = tree.tokens.items(.tag);
    const last: Ast.TokenIndex = @intCast(tree.tokens.len - 1);
    var k = call;
    while (k > 0) {
        k -= 1;
        if (!isDeferred(tags[k])) continue;
        // A deferred statement covers the call only if the call is one
        // of the tokens it covers; a `defer` that ended before it is a
        // different statement, however close the two are written.
        const stop = tokens.skipDeferStmt(tags, k, last) orelse continue;
        if (stop >= call) return true;
    }
    return false;
}

/// True iff `tag` opens a deferred statement.
fn isDeferred(tag: std.zig.Token.Tag) bool {
    return tag == .keyword_defer or tag == .keyword_errdefer;
}

// ── Reaching the copy: which acquire the copy cannot be read without ──
//
// The window an acquire is searched in is the whole enclosing body, and
// a window that wide is not a path: `if (keep) source.ref.retain();` sits
// in the body of `copy`, twenty tokens above the `return source;` that
// duplicates the reference — and on the paths where `keep` is false it has
// added nothing at all.  So what decides whether an acquire balances a
// copy is whether the copy can be reached WITHOUT it, and that is a
// question about the branches written around each of them.

/// One conditional extent of a body: the body of an `if` or of its
/// `else`, one `switch` prong, a `catch` / `orelse` payload, or a whole
/// loop — a loop may run zero times, so nothing written in one is on a
/// path the code outside it certainly took.
const ReachFrame = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// How many extents one window may hold before the reading of it stops.
/// Past the bound the window is UNKNOWN rather than unconditioned, which
/// charges the copy instead of balancing it — the same fail-closed answer
/// the scope resolution in `aligncast_on_byte_slice` gives when its brace
/// stack cannot hold the nesting it met.
const max_reach_frames = 128;

/// The conditional extents one window of a body contains.
const ReachFrames = struct {
    items: [max_reach_frames]ReachFrame = undefined,
    len: usize = 0,
    /// A window this rule could not read all the way — a construct whose
    /// extent no token closes, an extent that ends before it starts, or
    /// more extents than the bound holds — is UNKNOWN, not empty.  Two
    /// unknowns are not evidence of a shared path, so nothing in such a
    /// window is read as reaching the copy.
    unknown: bool = false,
};

/// True iff an acquire written at `call` runs on EVERY path that reaches
/// the copy at `copy`.
///
/// The branch an acquire is written inside is what decides it.  An acquire
/// in the `if` that guards the copy is the fix for that copy, and the same
/// acquire beside an unconditional copy is nothing: the copy makes the
/// second owner on the paths where the acquire never ran.  So the test is
/// containment, not count — every extent written at the acquire has to
/// hold the copy as well — and it is what keeps the correlated shape
/// (`if (c) { retain(); return source; } else { retain(); return source; }`)
/// quiet without letting any one arm's acquire answer for its neighbour.
fn reachesCopy(frames: *const ReachFrames, call: Ast.TokenIndex, copy: Ast.TokenIndex) bool {
    if (frames.unknown) return false;
    for (frames.items[0..frames.len]) |frame| {
        if (call < frame.first or call > frame.last) continue;
        if (copy < frame.first or copy > frame.last) return false;
    }
    return true;
}

/// Every conditional extent in `[first, last]`: the two arms of an `if`,
/// a whole loop, the body of each `switch` prong, and each `catch` /
/// `orelse` payload.
///
/// Two shapes are deliberately NOT extents.  A plain `{ … }` block is not
/// one: a block that has been written and left has run, whatever it held.
/// Neither is the condition of an `if`, a `switch` or a `catch`, which is
/// evaluated before either arm and on every path through the construct.
/// What is left out of that reading is the `and` / `or` right-hand side,
/// which runs only when the operand beside it holds.  It cannot carry an
/// acquire this rule reads: `retain()`, `clone()`, `dupeRef()` and the
/// rest of the acquire names return nothing to combine, so an acquire is
/// always a statement of its own and a statement is never an operand.
///
/// The walk visits every token rather than jumping from one construct's end
/// to the next, so an `if` nested inside another's arm is an extent of its
/// own and the copy it guards is read against it.
fn collectReachFrames(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    out: *ReachFrames,
) void {
    out.len = 0;
    out.unknown = false;
    if (first > last or @as(usize, last) >= tags.len) return;
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .keyword_if => collectIfArms(tags, t, last, out),
            .keyword_while, .keyword_for => collectLoop(tags, t, last, out),
            // `=>` tokenizes as `equal_angle_bracket_right`, and `.arrow`
            // is a name this walk used and the tokenizer no longer
            // emits: reading it collected no prong extent at all, so an
            // acquire in one prong balanced the copy in the next.
            .equal_angle_bracket_right => collectProng(tags, t, last, out),
            .keyword_catch, .keyword_orelse => collectPayload(tags, t, last, out),
            else => {},
        }
    }
}

/// The arms of the `if` at `if_tok`, each from the first token of what it
/// runs to the last token that belongs to it.
///
/// `else if` is the else's own body — the whole nested statement — and the
/// `if` inside it is read as an extent of its own by this same walk, so an
/// acquire in that condition answers for the arm it conditions and for
/// nothing else.
fn collectIfArms(
    tags: []const std.zig.Token.Tag,
    if_tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
    out: *ReachFrames,
) void {
    if (if_tok + 1 > last or tags[if_tok + 1] != .l_paren) return;
    const cond_close = tokens.matchParen(tags, if_tok + 1, last) orelse {
        out.unknown = true;
        return;
    };
    const then_start = armBodyStart(tags, cond_close + 1, last);
    const then_last = armBodyLast(tags, then_start, last, true) orelse {
        out.unknown = true;
        return;
    };
    addFrame(out, then_start, then_last);
    const else_tok = then_last + 1;
    if (else_tok > last or tags[else_tok] != .keyword_else) return;
    const else_start = armBodyStart(tags, else_tok + 1, last);
    const else_last = armBodyLast(tags, else_start, last, false) orelse {
        out.unknown = true;
        return;
    };
    addFrame(out, else_start, else_last);
}

/// A `while` / `for` as ONE extent, from the keyword to the last token of
/// its `else`: the loop may run zero times, so nothing inside it — least
/// of all the code a `for` iterates with — is on a path the loop certainly
/// took.  `inline while` / `inline for` are the same shape, `inline`
/// being its own token ahead of the keyword.
fn collectLoop(
    tags: []const std.zig.Token.Tag,
    kw: Ast.TokenIndex,
    last: Ast.TokenIndex,
    out: *ReachFrames,
) void {
    if (kw + 1 > last or tags[kw + 1] != .l_paren) return;
    const cond_close = tokens.matchParen(tags, kw + 1, last) orelse {
        out.unknown = true;
        return;
    };
    const body_start = armBodyStart(tags, cond_close + 1, last);
    var body_last = armBodyLast(tags, body_start, last, false) orelse {
        out.unknown = true;
        return;
    };
    const else_tok = body_last + 1;
    if (else_tok <= last and tags[else_tok] == .keyword_else) {
        const else_start = armBodyStart(tags, else_tok + 1, last);
        body_last = armBodyLast(tags, else_start, last, false) orelse {
            out.unknown = true;
            return;
        };
    }
    addFrame(out, kw, body_last);
}

/// The body of the prong the `=>` at `arrow` introduces, up to the comma
/// that ends it, the `;` of a `switch` written as a statement, or the `}`
/// that closes the switch.
fn collectProng(
    tags: []const std.zig.Token.Tag,
    arrow: Ast.TokenIndex,
    last: Ast.TokenIndex,
    out: *ReachFrames,
) void {
    const start = armBodyStart(tags, arrow + 1, last);
    if (start > last) return;
    var depth: u32 = 0;
    var t = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                if (depth == 0) {
                    addFrame(out, start, t -| 1);
                    return;
                }
                depth -= 1;
            },
            .comma, .semicolon => if (depth == 0) {
                addFrame(out, start, t -| 1);
                return;
            },
            else => {},
        }
    }
    addFrame(out, start, last);
}

/// The payload of the `catch` / `orelse` at `kw`: it runs on the path the
/// left-hand side FAILED, so an acquire written in one is not an acquire
/// the code after the expression ever saw.
fn collectPayload(
    tags: []const std.zig.Token.Tag,
    kw: Ast.TokenIndex,
    last: Ast.TokenIndex,
    out: *ReachFrames,
) void {
    const start = armBodyStart(tags, kw + 1, last);
    if (start > last) return;
    if (tags[start] == .l_brace) {
        // A payload the window cuts off runs to the end of it: the copy is
        // the last thing read, and a `}` that closed the payload before the
        // copy would be in the window for `matchBrace` to find.
        addFrame(out, start, tokens.matchBrace(tags, start, last) orelse last);
        return;
    }
    addFrame(out, start, statementLast(tags, start, last, false));
}

/// The first token of what an arm RUNS: past a loop's continue clause
/// (`while (cond) : (i += 1) body`), past the `|captures|` an `if`, a
/// `while`, a `for` or a prong may bind, and past the `label:` a block may
/// carry.
///
/// The continue clause has to be stepped over rather than read as the
/// body: taking it for one would walk the loop's `{ … }` as a balanced
/// group and go on to the `;` of whatever statement follows the loop,
/// which would put the whole of the rest of the body inside the loop's
/// extent and read an acquire that may never run as one that reaches the
/// copy written after it.
fn armBodyStart(tags: []const std.zig.Token.Tag, from: Ast.TokenIndex, last: Ast.TokenIndex) Ast.TokenIndex {
    var t = from;
    if (t + 1 <= last and tags[t] == .colon and tags[t + 1] == .l_paren) {
        const close = tokens.matchParen(tags, t + 1, last) orelse return last + 1;
        t = close + 1;
    }
    if (t <= last and tags[t] == .pipe) {
        var close: Ast.TokenIndex = t + 1;
        while (close <= last and tags[close] != .pipe) : (close += 1) {}
        t = if (close <= last) close + 1 else last + 1;
    }
    if (t + 1 <= last and tags[t] == .identifier and tags[t + 1] == .colon) t += 2;
    return t;
}

/// The last token of what an arm runs: the `}` closing its own block, or
/// the end of the one statement an arm written without braces is.  Null
/// when the arm runs no token this window holds at all.
///
/// `stop_at_else` is the one thing that separates an `if`'s then-arm from
/// every other arm: an `else` written at the top level of that expression
/// belongs to the `if`, not to the arm, so `if (keep) source.ref.retain()
/// else return source;` runs no further than the `)`.  Reading that arm as
/// the whole statement would put the else's own copy inside it and answer
/// the else's question with the then-arm's acquire.
///
/// A block the window does not close runs to the end of the window.  The
/// copy is the last thing read, so an arm the window cuts off is still
/// open around it — and had it closed before the copy, the closing `}`
/// would be in the window and this would have found it.
fn armBodyLast(
    tags: []const std.zig.Token.Tag,
    from: Ast.TokenIndex,
    last: Ast.TokenIndex,
    stop_at_else: bool,
) ?Ast.TokenIndex {
    if (from > last) return null;
    if (tags[from] == .l_brace) return tokens.matchBrace(tags, from, last) orelse last;
    return statementLast(tags, from, last, stop_at_else);
}

/// The last token of the one statement written at `from`: the `;` that
/// ends it, or the token before the `}` that closes the block it stands
/// in — Zig lets a statement end at either.
fn statementLast(
    tags: []const std.zig.Token.Tag,
    from: Ast.TokenIndex,
    last: Ast.TokenIndex,
    stop_at_else: bool,
) Ast.TokenIndex {
    var depth: u32 = 0;
    var t = from;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                if (depth == 0) return t -| 1;
                depth -= 1;
            },
            .semicolon => if (depth == 0) return t,
            .keyword_else => if (stop_at_else and depth == 0) return t -| 1,
            else => {},
        }
    }
    return last;
}

/// Record one extent.  An extent that ends before it starts is a reading
/// this rule could not make out, and neither is a window with more of them
/// than the fixed bound holds: both leave the copy charged.
fn addFrame(out: *ReachFrames, first: Ast.TokenIndex, last: Ast.TokenIndex) void {
    if (last < first or out.len == out.items.len) {
        out.unknown = true;
        return;
    }
    out.items[out.len] = .{ .first = first, .last = last };
    out.len += 1;
}

/// True iff this body binds an immutable local from `source_recv .
/// source_field` and acquires through it as the very next statement:
///
///   const r = source.ref.?;
///   r.retain();
///
/// The binding is read from the memoized `LocalBindings` seam this
/// codebase resolves every "what was this name bound from" question
/// with, so each condition is a fact rather than a guess:
///
///   * it is a `const` local written directly in this body.  The seam
///     does not track reassignment, so a `var` could be rebound between
///     the binding and the acquire; a `.param` or `.loop_capture` binding
///     is not an ordinary alias of anything; and a binding inside a block
///     sits under a condition that may decide whether the acquire runs
///     at all.
///   * its initializer is EXACTLY `source . field`, unwrapped or not.
///     Nothing else may sit on the right-hand side, so the local holds a
///     second owner of the one reference this copy duplicates — not a
///     member of the field, and not some other value that borrows the
///     name `source`.
///   * the receiver at that initializer resolves to the PARAMETER
///     itself, never to a local that shadows the parameter's name.
///   * the acquire is the statement immediately after the binding, so
///     the binding is provably in scope at the use: nothing can shadow,
///     rebind, `defer` or conditionally skip between them.  The seam's
///     `findAt` then confirms, at the acquire's own token, that the name
///     means this binding and not another declaration of it.
///
/// One hop only — the initializer is a field of the source, never
/// another alias — so there is no chain to bound and no cycle to
/// detect.  An unreadable seam declines (false) and leaves the copy
/// reported: the wrong verdict here would be silence.
fn hasAliasRefAcquireCall(
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    body_first: Ast.TokenIndex,
    before_copy: Ast.TokenIndex,
    source_recv: []const u8,
    source_field: []const u8,
) bool {
    const bindings = cache.localBindings(proto, body) catch return false;
    for (bindings.items) |*b| {
        if (!b.is_const) continue;
        switch (b.origin) {
            .param, .loop_capture => continue,
            else => {},
        }
        // Written directly in this body, not inside a block below it: the
        // only brace left open at the binding's own declaration is the
        // body's own.  The seam carries no scope index, so the depth is
        // read off the tokens instead of off a field that no longer
        // exists.
        if (!writtenAtBodyTopLevel(tags, body_first, b.name_token)) continue;
        const rhs_first = b.rhs_first;
        if (rhs_first + 2 > b.rhs_last) continue;
        if (tags[rhs_first] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(rhs_first), source_recv)) continue;
        if (tags[rhs_first + 1] != .period) continue;
        if (tags[rhs_first + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(rhs_first + 2), source_field)) continue;
        // `= source . field ;` or `= source . field . ? ;`, nothing more.
        const is_field = b.rhs_last == rhs_first + 2;
        const is_unwrapped_field = b.rhs_last == rhs_first + 4 and
            tags[rhs_first + 3] == .period and
            tags[rhs_first + 4] == .question_mark;
        if (!is_field and !is_unwrapped_field) continue;
        // The receiver is the parameter, not a local shadowing it.
        const receiver = bindings.findAt(source_recv, rhs_first) orelse continue;
        switch (receiver.origin) {
            .param => {},
            else => continue,
        }
        // The acquire statement, immediately after this binding's `;`.
        const call = b.rhs_last + 2;
        if (call + 3 > before_copy) continue;
        if (tags[call] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(call), b.name)) continue;
        if (tags[call + 1] != .period) continue;
        if (tags[call + 2] != .identifier) continue;
        if (!method_names.isRefAcquireName(tree.tokenSlice(call + 2))) continue;
        if (tags[call + 3] != .l_paren) continue;
        // The name means THIS binding where the acquire is written.
        const used = bindings.findAt(b.name, call) orelse continue;
        if (used.name_token != b.name_token) continue;
        return true;
    }
    return false;
}

/// True when the declaration whose name sits at `name_token` is written
/// directly in the body `body_first` opens — no block below it stands
/// between the two.  Tokens are already lexed, so a brace inside a
/// string or a comment is one token of another kind and never moves
/// the depth.
fn writtenAtBodyTopLevel(tags: []const std.zig.Token.Tag, body_first: Ast.TokenIndex, name_token: Ast.TokenIndex) bool {
    if (name_token <= body_first) return false;
    var depth: u32 = 0;
    var t = body_first + 1;
    while (t < name_token) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => if (depth > 0) {
                depth -= 1;
            },
            else => {},
        }
    }
    return depth == 0;
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

fn reportWholeCopy(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    source_tok: Ast.TokenIndex,
    source: []const u8,
    type_name: []const u8,
    owned: OwnedRef,
) !void {
    // What fixes the copy follows what the teardown does with the field.
    // An acquire is the fix only where the declaration drives the field
    // through a reference protocol of its own; naming one where the field
    // is handed to something that frees it outright would point the
    // reader at a fix that does not exist.
    //
    // `.borrowed_argument` cannot reach here — a field the callee
    // borrows is not one this declaration gives back, so it is no
    // field of the copy at all.  It shares the unread arm rather than
    // leaving a payload unhandled, so a verdict that did reach this
    // switch would still be charged instead of silencing the copy.
    const fix = switch (owned.payload) {
        .protocol => try std.fmt.allocPrint(
            gpa,
            "acquire a second reference first (`{s}.{s}` retain/ref/clone, or an equivalent ref-acquire method), or hand the parameter on instead of copying it",
            .{ source, owned.field },
        ),
        .destroyed_argument, .freed_receiver => try std.fmt.allocPrint(
            gpa,
            "hand the parameter on instead of copying it — that teardown takes `.{s}` apart itself, so a second reference would not keep the two owners apart",
            .{owned.field},
        ),
        .borrowed_argument, .unknown => try std.fmt.allocPrint(
            gpa,
            "hand the parameter on instead of copying it — this file cannot read what the teardown does with `.{s}`, so it cannot say an acquire would keep the two owners apart",
            .{owned.field},
        ),
    };
    defer gpa.free(fix);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` is copied by value out of a by-value parameter of type `{s}` without acquiring a second reference — `{s}.{s}` hands the reference its `.{s}` field holds back on cleanup, so the copy and the parameter both give one reference back, which can double-free the shared object or SIGFPE; {s}",
        .{ source, type_name, type_name, owned.method, owned.field, fix },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, source_tok),
        .end = Pos.fromTokenEnd(tree, source_tok),
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

// ── Borrowed pointer views vs. owning handles ─────────────────────────
//
// The lifecycle evidence this rule collects is keyed on the FIELD SPELLING
// alone, so once any type in the file really does acquire/release its
// `data`, every other same-spelled field in that file looks like a
// refcounted owner too.  A borrowed pointer view — a field that hands back
// a raw pointer and declares no teardown — shares the owner's reference
// instead of duplicating it, so copying the pointer acquires nothing and
// must stay quiet.
//
// What decides it is the DESTINATION DECLARATION, not the spelling: the
// struct-init's type expression, the declared type of the field being
// initialised, and whether THAT type runs a reference protocol on the
// field.  `View` / `Cursor` below never decrement anything; `Plan`,
// `Owner` and `Handle` genuinely do.  A pointer destination is therefore
// not suppressed blanket-wise — only a destination that declares no
// ownership protocol on the field is.

test "ref-counted-copy-without-dupe: copying into a borrowed view does not demand an acquire" {
    // Issue #53.  `plan` owns the snapshot and returns a reference on
    // teardown; `View` merely borrows it and has no destructor at all, so
    // dropping a view never decrements anything.  The copy acquires
    // nothing and nothing needs acquiring — the rule must stay quiet even
    // though this file's `data` field really does have a lifecycle.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn acquire(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self.refs);
        \\        }
        \\    }
        \\};
        \\
        \\/// The owner: `data` is a reference this type hands back.
        \\const Plan = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Plan) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\};
        \\
        \\/// A borrowed view.  No destructor, no acquire, no release: the
        \\/// plan stays the owner and the view only reads.
        \\const View = struct {
        \\    data: ?*const Snapshot,
        \\};
        \\
        \\fn borrow(plan: Plan) View {
        \\    const view = View{ .data = plan.data };
        \\    return view;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a borrowed non-optional pointer view is not an owner" {
    // The same protocol decision as the optional view, spelled without the
    // `?`: a required `*const` field whose destination declares no
    // teardown is still a borrow.  A fix that only inspects optional
    // pointer shapes must not leave this one firing.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn acquire(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self.refs);
        \\        }
        \\    }
        \\};
        \\
        \\/// The owner: `data` is a reference this type hands back.
        \\const Plan = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Plan) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\};
        \\
        \\/// A borrowed cursor.  No destructor, so the plan keeps the only
        \\/// reference and the copy is free.
        \\const Cursor = struct {
        \\    data: *const Snapshot,
        \\};
        \\
        \\fn cursorFor(plan: Plan) Cursor {
        \\    const cursor = Cursor{ .data = plan.data };
        \\    return cursor;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: an owning pointer destination still warns" {
    // The destination DECLARES the ownership protocol — its `deinit`
    // decrements the copied reference — so the copy is a real missing
    // acquisition even though the field is a pointer.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn acquire(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self.refs);
        \\        }
        \\    }
        \\};
        \\
        \\/// Owns its snapshot outright: `deinit` returns the reference.
        \\const Owner = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Owner) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\};
        \\
        \\fn duplicate(other: Owner) Owner {
        \\    return Owner{ .data = other.data, .gpa = other.gpa };
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: an optional owning pointer destination still warns" {
    // Optionality alone does not make a field a borrow: this destination
    // releases the reference whenever it is present, so the unacquired copy
    // is still a missing acquisition.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn acquire(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self.refs);
        \\        }
        \\    }
        \\};
        \\
        \\/// `data` is a genuine ownership handle in THIS type.
        \\const Owner = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Owner) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\};
        \\
        \\/// The same handle, held only when there is a snapshot to hold.
        \\/// An absent `data` leaks nothing; a present one is owned.
        \\const Handle = struct {
        \\    data: ?*const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Handle) void {
        \\        if (self.data) |snap| snap.release(self.gpa);
        \\    }
        \\};
        \\
        \\fn duplicate(other: Handle) Handle {
        \\    return Handle{ .data = other.data, .gpa = other.gpa };
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: the owner is reported, not the borrow beside it" {
    // One file, one field spelling, two destinations.  `Plan` releases
    // what it holds; `View` only borrows the same pointer.  The verdict
    // belongs to the destination, so exactly one report is raised and it
    // is the `Plan` copy — the `View` copy, one line away, is silent.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) gpa.free(self.refs);
        \\    }
        \\};
        \\
        \\const Plan = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Plan) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\};
        \\
        \\/// Borrows the plan's snapshot; nothing here will ever release it.
        \\const View = struct {
        \\    data: ?*const Snapshot,
        \\};
        \\
        \\fn duplicate(plan: Plan) Plan {
        \\    return Plan{ .data = plan.data, .gpa = plan.gpa };
        \\}
        \\
        \\fn borrow(doc: Plan) View {
        \\    return View{ .data = doc.data };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`plan.data`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "doc.data") == null);
}

test "ref-counted-copy-without-dupe: an owner stays an owner when its protocol lives in another method" {
    // The pointer field is not what makes anything an owner — the
    // declaration actually running a release ON that field is.  Here
    // `deinit` only forwards; the release itself is one call away.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) gpa.free(self.refs);
        \\    }
        \\};
        \\
        \\const Owner = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn releaseData(self: *Owner) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\
        \\    pub fn deinit(self: *Owner) void {
        \\        self.releaseData();
        \\    }
        \\};
        \\
        \\fn duplicate(other: Owner) Owner {
        \\    return Owner{ .data = other.data, .gpa = other.gpa };
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a borrowed view reached through a qualified name stays quiet" {
    // The declaration is named `Registry.View`, not `View`; binding the
    // literal's type expression has to resolve the qualified path or the
    // verdict silently falls back to "unknown" and the borrow is lost.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) gpa.free(self.refs);
        \\    }
        \\};
        \\
        \\const Registry = struct {
        \\    pub const Plan = struct {
        \\        data: *const Snapshot,
        \\        gpa: std.mem.Allocator,
        \\
        \\        pub fn deinit(self: *Plan) void {
        \\            self.data.release(self.gpa);
        \\        }
        \\    };
        \\
        \\    /// Reads the plan's snapshot through a pointer and never
        \\    /// releases anything of its own.
        \\    pub const View = struct {
        \\        data: ?*const Snapshot,
        \\    };
        \\};
        \\
        \\fn borrow(doc: Registry.Plan) Registry.View {
        \\    return Registry.View{ .data = doc.data };
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a destination that declares no protocol is still reported" {
    // Silence needs a POINTER and no protocol together.  A destination
    // that wraps an owning value and declares no teardown is the
    // historical case, not a borrow: the caller may well run the
    // wrapped type's destructor on the copy, and the file has already
    // shown it owns a `name`.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const OwnedName = struct {
        \\    text: []const u8,
        \\
        \\    pub fn deinit(self: *OwnedName, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.text);
        \\    }
        \\};
        \\
        \\/// Evidence that this file really does own a `name` somewhere.
        \\const Store = struct {
        \\    name: OwnedName,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Store) void {
        \\        self.name.deinit();
        \\    }
        \\};
        \\
        \\const Wrapper = struct {
        \\    name: OwnedName,
        \\    gpa: std.mem.Allocator,
        \\};
        \\
        \\fn duplicate(other: Wrapper) Wrapper {
        \\    return Wrapper{ .name = other.name, .gpa = other.gpa };
        \\}
        \\
    );
}

// ── Whole-value copies of an owning handle ─────────────────────────
//
// A struct literal is not the only way one reference becomes two.  A
// by-value PARAMETER is itself copied into the frame, so handing that
// parameter on — `return source;` — gives the caller a second owner
// of the one reference it holds.  Every fixture below decides on the
// SOURCE declaration: `Shared.deref` hands its `ref` field back, and
// the spelling of that field decides nothing.

test "ref-counted-copy-without-dupe: a whole owning handle returned by value is reported" {
    // Issue #53's control.  `Shared` holds one `*Snapshot` and gives
    // the reference back in its own `deref`; `return source;` copies
    // the whole handle without acquiring anything, so both sides
    // decrement one refcount.  The only spelling that differs from the
    // recorded case is the `retain` receiver: a mutable pointer is
    // what the compiler accepts for an increment, and the verdict
    // reads method names, not receivers.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    ref: *Snapshot,
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        self.ref.deref(gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    // Copying the handle without acquiring a second reference
        \\    // means both sides decrement on drop.
        \\    return source;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a whole copy that acquires its own reference is quiet" {
    // The same handle, the same copy, and the acquire that balances
    // it.  `source.ref.retain()` is one reference added for the second
    // owner the copy creates, so nothing is missing here.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    ref: *Snapshot,
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        self.ref.deref(gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    source.ref.retain();
        \\    return source;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a whole borrowed view copied by value is quiet" {
    // `Plan` owns the snapshot and gives the reference back; `View`
    // declares no destructor at all, so dropping a view decrements
    // nothing and copying one duplicates nothing.  One file, one field
    // spelling, two declarations — the verdict belongs to the one the
    // copy is made of.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn acquire(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self.refs);
        \\        }
        \\    }
        \\};
        \\
        \\/// The owner: `data` is a reference this type hands back.
        \\const Plan = struct {
        \\    data: *const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Plan) void {
        \\        self.data.release(self.gpa);
        \\    }
        \\};
        \\
        \\/// A borrowed view.  No destructor, so the plan keeps the
        \\/// only reference and a copy of the view is free.
        \\const View = struct {
        \\    data: *const Snapshot,
        \\};
        \\
        \\pub fn duplicate(view: View) View {
        \\    return view;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a whole copy of a value-typed owner is reported" {
    // The pointer spelling is not what makes an owner.  This handle
    // holds an owning VALUE and forwards its teardown, so a whole-value
    // copy hands two holders the same storage — the same verdict the
    // struct-init path already reaches for `.name = other.name`.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const OwnedName = struct {
        \\    text: []const u8,
        \\
        \\    pub fn deinit(self: *OwnedName, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.text);
        \\    }
        \\};
        \\
        \\const Store = struct {
        \\    name: OwnedName,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Store) void {
        \\        self.name.deinit();
        \\    }
        \\};
        \\
        \\pub fn copy(source: Store) Store {
        \\    return source;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a pointer parameter hands over an address, not a handle" {
    // `*Shared` is an address: copying it duplicates no reference count,
    // because the `Shared` behind it — and the one reference it holds —
    // belongs to whoever allocated it.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    ref: *Snapshot,
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        self.ref.deref(gpa);
        \\    }
        \\};
        \\
        \\pub fn same(handle: *Shared) *Shared {
        \\    return handle;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a lease that writes through a borrowed handle is not an owner" {
    // `Lease.release` only writes THROUGH the state it borrows and
    // frees nothing of its own, so no reference is handed back and a
    // copy of a lease duplicates none.  The instance destructor exists;
    // what it destroys is somebody else's storage.
    try testing.expectNoFireTyped(check,
        \\const State = struct {
        \\    claimed: bool = false,
        \\    active: bool = true,
        \\};
        \\
        \\const Lease = struct {
        \\    state: *State,
        \\    generation: u64 = 1,
        \\
        \\    pub fn release(self: Lease) void {
        \\        if (self.state.claimed) return;
        \\        self.state.active = false;
        \\        self.state.claimed = true;
        \\    }
        \\};
        \\
        \\pub fn extend(lease: Lease) Lease {
        \\    return lease;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a static free callback is not this value's destructor" {
    // `fn free(ctx: *anyopaque, bytes: []u8)` is an allocator interface
    // callback with no receiver: the buffer it frees belongs to
    // whoever allocated it.  Counting it as this type's destructor
    // would report every by-value copy of a buffer header.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Region = struct {
        \\    ctx: *anyopaque,
        \\    bytes: []u8,
        \\
        \\    pub fn free(ctx: *anyopaque, bytes: []u8) void {
        \\        const gpa: *std.mem.Allocator = @ptrCast(@alignCast(ctx));
        \\        gpa.free(bytes);
        \\    }
        \\};
        \\
        \\pub fn duplicate(region: Region) Region {
        \\    return region;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: a plain value type has no reference to duplicate" {
    // No declaration, so no protocol: copying `Point` by value shares
    // no heap storage and there is nothing to acquire.
    try testing.expectNoFireTyped(check,
        \\const Point = struct {
        \\    x: f32,
        \\    y: f32,
        \\};
        \\
        \\pub fn duplicate(point: Point) Point {
        \\    return point;
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: one duplicated handle is one report, at the copy" {
    // `const alias = source;` is where the second owner appears; the
    // `return alias;` after it hands that same second owner on, so it
    // is the same defect and not a second one.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *Snapshot) void {
        \\        self.refs.* -= 1;
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    ref: *Snapshot,
        \\
        \\    pub fn deref(self: *Shared) void {
        \\        self.ref.release();
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    const alias = source;
        \\    return alias;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`Shared`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: the recorded issue-#53 borrowed case stays quiet" {
    // `issue53_borrowed.zig` verbatim.  The whole-value pass has nothing
    // to decide here on its own terms: `borrow` takes the plan by
    // POINTER, so handing it on copies an address, and `dupeRef`'s
    // `return copy;` returns a local it just built — a move, not a
    // second owner.  This pins the recorded quiet verdict against the
    // pass added for #53c1.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn dupeRef(self: *const Snapshot, gpa: std.mem.Allocator) !*Snapshot {
        \\        const copy = try gpa.create(Snapshot);
        \\        copy.* = .{ .bytes = try gpa.dupe(u8, self.bytes), .refcount = 1 };
        \\        return copy;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\const Plan = struct {
        \\    data: ?*const Snapshot,
        \\
        \\    pub fn teardown(self: *Plan, gpa: std.mem.Allocator) void {
        \\        if (self.data) |snapshot| {
        \\            // `plan` owns the reference; releasing it here is the owner's job.
        \\            @constCast(snapshot).deref(gpa);
        \\        }
        \\    }
        \\};
        \\
        \\const View = struct {
        \\    data: ?*const Snapshot,
        \\};
        \\
        \\pub fn borrow(plan: *const Plan) View {
        \\    // The view only borrows; dropping it never decrements anything.
        \\    return .{ .data = plan.data };
        \\}
        \\
    );
}

test "ref-counted-copy-without-dupe: the recorded issue-#53 non-optional borrowed case stays quiet" {
    // `issue53_required.zig` verbatim: the same borrowed view with the
    // optional dropped from its field.  Two borrow spellings, one
    // recorded quiet verdict each.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn dupeRef(self: *const Snapshot, gpa: std.mem.Allocator) !*Snapshot {
        \\        const copy = try gpa.create(Snapshot);
        \\        copy.* = .{ .bytes = try gpa.dupe(u8, self.bytes), .refcount = 1 };
        \\        return copy;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\const Plan = struct {
        \\    data: ?*const Snapshot,
        \\
        \\    pub fn teardown(self: *Plan, gpa: std.mem.Allocator) void {
        \\        if (self.data) |snapshot| {
        \\            // `plan` owns the reference; releasing it here is the owner's job.
        \\            @constCast(snapshot).deref(gpa);
        \\        }
        \\    }
        \\};
        \\
        \\const View = struct {
        \\    data: *const Snapshot,
        \\};
        \\
        \\pub fn borrow(plan: *const Plan) View {
        \\    // The view only borrows; dropping it never decrements anything.
        \\    return .{ .data = plan.data.? };
        \\}
        \\
        \\pub fn borrowRequired(plan: *const Plan) View {
        \\    return .{ .data = plan.data.? };
        \\}
        \\
    );
}

// ── Whole-value copies of a handle with TWO owning fields ──────────
//
// One whole-value copy duplicates one reference for every field the
// SOURCE declaration hands back, so a handle that gives two of them
// back needs two acquires to balance — and acquiring only the field
// declared first must silence nothing.  The two fixtures below are the
// same handle with its fields declared in both orders, so no verdict
// can depend on which of them happens to come first.

/// `Shared.deref` hands back the reference `ref` holds and
/// `Shared.drop` the one `tail` holds: two owners released by two
/// different instance methods, neither of them static.
const two_owners_ref_first =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    bytes: []u8,
    \\    refcount: u64 = 1,
    \\
    \\    pub fn retain(self: *Snapshot) void {
    \\        self.refcount += 1;
    \\    }
    \\
    \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refcount -= 1;
    \\        if (self.refcount == 0) {
    \\            gpa.free(self.bytes);
    \\            gpa.destroy(self);
    \\        }
    \\    }
    \\};
    \\
    \\const Shared = struct {
    \\    ref: *Snapshot,
    \\    tail: *Snapshot,
    \\
    \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
    \\        self.ref.deref(gpa);
    \\    }
    \\
    \\    pub fn drop(self: *Shared, gpa: std.mem.Allocator) void {
    \\        self.tail.deref(gpa);
    \\    }
    \\};
    \\
;

/// The same handle with the same method-to-field mapping, declared in
/// the other order.
const two_owners_tail_first =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    bytes: []u8,
    \\    refcount: u64 = 1,
    \\
    \\    pub fn retain(self: *Snapshot) void {
    \\        self.refcount += 1;
    \\    }
    \\
    \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refcount -= 1;
    \\        if (self.refcount == 0) {
    \\            gpa.free(self.bytes);
    \\            gpa.destroy(self);
    \\        }
    \\    }
    \\};
    \\
    \\const Shared = struct {
    \\    tail: *Snapshot,
    \\    ref: *Snapshot,
    \\
    \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
    \\        self.ref.deref(gpa);
    \\    }
    \\
    \\    pub fn drop(self: *Shared, gpa: std.mem.Allocator) void {
    \\        self.tail.deref(gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a whole copy that acquires only the first-declared owning field is reported on the other" {
    // `source.ref.retain()` balances the second owner of the reference
    // `Shared.deref` releases, and nothing else: `tail` is now owned by
    // both the copy and the parameter, and `Shared.drop` gives it back
    // twice.  The one finding names the field left unacquired.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.tail`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") == null);
}

test "ref-counted-copy-without-dupe: the same copy is reported whichever owning field is declared first" {
    // The same two fields, the same acquire on the field declared
    // first — and the finding follows the UNACQUIRED field rather than
    // the declaration order, naming `ref` this time.
    const src = two_owners_tail_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.tail.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.tail`") == null);
}

test "ref-counted-copy-without-dupe: a whole copy that acquires only the second-declared owning field is reported" {
    // An acquire on ONE of the declaration's references balances one
    // owner, not two.  `source.tail.retain()` leaves `ref` — the field
    // this declaration declares first, and the one an acquire on the
    // first field would have balanced — duplicated, so the copy is
    // still reported.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.tail.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.tail`") == null);
}

test "ref-counted-copy-without-dupe: a whole copy that acquires neither owning field is reported once" {
    // Both references are duplicated and one report is the whole
    // verdict for this copy site: the second unacquired field is the
    // same defect seen from another field, not a second defect.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: a whole copy that acquires every owning field is quiet" {
    // One acquire per reference the declaration hands back: the copy
    // and the parameter each give one reference back, which is exactly
    // what the two holders own.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.ref.retain();
        \\    source.tail.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: acquires on another source do not balance this copy" {
    // `alias` holds references of its own; retaining them balances the
    // owner `alias` already has, not the one `source` hands to the
    // copy.  An acquire that does not reach the copy's own source and
    // field duplicates nothing here, so the copy stays reported.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared, alias: Shared) Shared {
        \\    alias.ref.retain();
        \\    alias.tail.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.tail`") == null);
}

// ── Which acquire actually balances a whole-value copy ──────────
//
// An acquire balances a copy only when it is a CALL on the copy's own
// source and the field that copy duplicates.  Every fixture below is
// built to fail for one spelling that reads like a balancing acquire
// and is not, or to pass for the spelling that is one.

/// `Shared` holds two OPTIONAL references and hands both back through
/// `deref`, so the fix for each field is written through its unwrap.
const optional_two_owners =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    bytes: []u8,
    \\    refcount: u64 = 1,
    \\
    \\    pub fn retain(self: *Snapshot) void {
    \\        self.refcount += 1;
    \\    }
    \\
    \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refcount -= 1;
    \\        if (self.refcount == 0) {
    \\            gpa.free(self.bytes);
    \\            gpa.destroy(self);
    \\        }
    \\    }
    \\};
    \\
    \\const Shared = struct {
    \\    ref: ?*Snapshot,
    \\    tail: ?*Snapshot,
    \\
    \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
    \\        if (self.ref) |r| {
    \\            r.deref(gpa);
    \\        }
    \\        if (self.tail) |t| {
    \\            t.deref(gpa);
    \\        }
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: an acquire on a member of the field does not balance it" {
    // `source.handle.ref` is a member of the node `handle` points at.
    // Retaining it balances the reference `Node.ref` holds; the node
    // reference `Shared.deref` gives back is still two owners after the
    // copy.  The name `ref` is an acquire name, but nothing is called on
    // the field itself.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\/// `ref` here is a member spelled like an acquire method.
        \\const Node = struct {
        \\    ref: *Snapshot,
        \\
        \\    pub fn deref(self: *Node, gpa: std.mem.Allocator) void {
        \\        self.ref.deref(gpa);
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    handle: *Node,
        \\
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        self.handle.deref(gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    source.handle.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.handle`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") == null);
}

test "ref-counted-copy-without-dupe: an acquire name taken as a value does not balance the copy" {
    // `keep` is the acquire as a function pointer; calling it is
    // somebody else's business.  `tail` is acquired for real, and the
    // copy is still reported on the field that was not.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    const keep = source.ref.retain;
        \\    _ = keep;
        \\    source.tail.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.tail`") == null);
}

test "ref-counted-copy-without-dupe: a member named after the parameter does not acquire it" {
    // `wrapper.source` is a field of `Wrapper`; retaining it balances
    // the owner `wrapper` already has, not the reference this copy
    // hands to its caller.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    ref: ?*Snapshot,
        \\
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        if (self.ref) |r| {
        \\            r.deref(gpa);
        \\        }
        \\    }
        \\};
        \\
        \\const Wrapper = struct {
        \\    source: ?*Snapshot,
        \\};
        \\
        \\pub fn copy(source: Shared, wrapper: Wrapper) Shared {
        \\    wrapper.source.?.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: an optional field acquired through its unwrap is quiet" {
    // `source.ref.?.retain()` is the acquire a `?*Snapshot` field is
    // balanced with — the same unwrap the declaration side reads in
    // `self.f.?.release(…)`.  One per field the handle hands back.
    const src = optional_two_owners ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.ref.?.retain();
        \\    source.tail.?.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: an unwrap acquire on one optional field leaves the other unacquired" {
    // The unwrap credits the field it is written on, and only that
    // one: `ref` is still two owners after the copy.
    const src = optional_two_owners ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.tail.?.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.tail`") == null);
}

test "ref-counted-copy-without-dupe: an unwrap acquire on another source does not balance this copy" {
    const src = optional_two_owners ++
        \\pub fn copy(source: Shared, alias: Shared) Shared {
        \\    alias.ref.?.retain();
        \\    alias.tail.?.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: a field acquired through a local bound from it is quiet" {
    // `r` is bound from `source.ref` itself — same parameter, same
    // field, unwrapped — and the acquire is the statement right after
    // it, so nothing can shadow, rebind or skip between them.
    const src = optional_two_owners ++
        \\pub fn copy(source: Shared) Shared {
        \\    const r = source.ref.?;
        \\    r.retain();
        \\    const t = source.tail.?;
        \\    t.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: a local bound inside a branch does not balance the copy" {
    // `verbose` decides whether the acquire ever runs, so it cannot be
    // read as one that certainly reaches the copy.
    const src = optional_two_owners ++
        \\pub fn copy(source: Shared, verbose: bool) Shared {
        \\    if (verbose) {
        \\        const r = source.ref.?;
        \\        r.retain();
        \\        const t = source.tail.?;
        \\        t.retain();
        \\    }
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: a local bound from another value does not balance the copy" {
    // Same local name, same field name, same acquire — but the value it
    // was bound from is `alias`'s reference, not the one this copy
    // duplicates.
    const src = optional_two_owners ++
        \\pub fn copy(source: Shared, alias: Shared) Shared {
        \\    const r = alias.ref.?;
        \\    r.retain();
        \\    const t = alias.tail.?;
        \\    t.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

// ── Which field a teardown hands back, and which method ──────────
//
// The verdict belongs to the DECLARATION, so the body has to be read as
// what it says: a capture is bound from its own scrutinee, storage
// handed to an allocator is a release of the field it was handed, and
// the method to open is the enclosing one.

test "ref-counted-copy-without-dupe: an allocator passed as an argument is not a captured name" {
    // `gpa` appears in this body only as the argument to
    // `d.release(self.gpa)`.  The capture `|d|` is bound from `data`,
    // so it says nothing about the allocator — and no acquire is
    // demanded of a field the declaration never gives back.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn retain(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self.refs);
        \\        }
        \\    }
        \\};
        \\
        \\const Handle = struct {
        \\    data: ?*const Snapshot,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Handle) void {
        \\        if (self.data) |d| {
        \\            d.release(self.gpa);
        \\        }
        \\    }
        \\};
        \\
        \\pub fn copy(source: Handle) Handle {
        \\    source.data.?.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

/// `name` is destroyed THROUGH the allocator field and never called on,
/// so it is still a reference this handle gives back.  `Registry` is
/// what gives the file a lifecycle call on that spelling at all.
const sibling_destroy_owner =
    \\const std = @import("std");
    \\
    \\const OwnedName = struct {
    \\    text: []const u8,
    \\
    \\    pub fn deinit(self: *OwnedName, gpa: std.mem.Allocator) void {
    \\        gpa.free(self.text);
    \\    }
    \\};
    \\
    \\const Registry = struct {
    \\    name: *OwnedName,
    \\
    \\    pub fn drop(self: *Registry, gpa: std.mem.Allocator) void {
    \\        self.name.deinit(gpa);
    \\    }
    \\};
    \\
    \\const Owner = struct {
    \\    name: *OwnedName,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn deinit(self: *Owner) void {
    \\        self.gpa.destroy(self.name);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a pointee destroyed through a sibling field is owned" {
    // `Owner.deinit` never calls a method on `name`; it hands the field
    // to `self.gpa.destroy`.  The pointer spelling does not turn an owned
    // field into a borrowed one.
    const src = sibling_destroy_owner ++
        \\pub fn copy(source: Owner) Owner {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
}

test "ref-counted-copy-without-dupe: a pointee destroyed through a sibling field is owned in a literal too" {
    // The same declaration, read as the destination of a struct literal:
    // `.name = other.name` duplicates the reference `Owner.deinit`
    // destroys, and the borrowed-view suppression is for views that
    // release nothing.
    const src = sibling_destroy_owner ++
        \\pub fn duplicate(other: Owner) Owner {
        \\    return .{ .name = other.name, .gpa = other.gpa };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "other.name") != null);
}

// ── A struct literal is read through its destination ──────────────
//
// What decides the copy is the declaration the literal constructs:
// what its teardown does with the field, and whether it is a pointer
// the declaration merely borrows.  The field's spelling and whatever
// lifecycle calls the rest of the file happens to make on the same name
// are a fallback for a destination that cannot be read at all — never a
// gate on one that can.  Each fixture below breaks a different one of
// those coarse readings, so a reader that keeps any of it as a gate has
// something to report nowhere.

/// A field nothing in this file acquires or releases under its own
/// name: the teardown binds `held` from it and drives the protocol
/// through that.  The spelling never appears in a
/// `recv . field . method (` chain anywhere, and `slot` is not a word
/// that suggests an owned field either, so both coarse readings find
/// nothing here — while the declaration still hands the reference back.
const derived_teardown_owner =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    refs: *usize,
    \\    bytes: []const u8,
    \\
    \\    pub fn retain(self: *const Snapshot) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        if (self.refs.* == 0) gpa.free(self.bytes);
    \\    }
    \\};
    \\
    \\const Registry = struct {
    \\    gpa: std.mem.Allocator,
    \\    slot: *Snapshot,
    \\
    \\    pub fn deinit(self: *Registry) void {
    \\        const held = self.slot;
    \\        held.release(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: an owned field no spelling in the file evidences is still read through its declaration" {
    // `Registry.deinit` really does release what `slot` holds, through a
    // name derived from it, so `.slot = source.slot` hands that
    // reference to a second owner and nothing acquires one.  Neither the
    // name nor anything else in this file says "lifecycle", and the
    // declaration says it plainly.
    const src = derived_teardown_owner ++
        \\pub fn copy(source: Registry) Registry {
        \\    return Registry{ .slot = source.slot, .gpa = source.gpa };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.slot`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "source.slot") != null);
}

/// The cross-side case with nothing else in the file naming
/// `other_ref`.  `Holder.deinit` hands it to `Node.free` beside a head
/// whose own free is perfectly visible, and `Node.free` forwards it on
/// to `finishOther`.  The head being a known receiver says nothing about
/// the argument written beside it, and no lifecycle call is ever made
/// on the argument's own name — so the file evidences the head and not
/// this field, which is exactly the field a copy duplicates.
const forwarded_argument_without_evidence =
    \\const std = @import("std");
    \\
    \\const OtherRef = struct {
    \\    refs: u32 = 1,
    \\    bytes: []u8,
    \\
    \\    pub fn retain(self: *OtherRef) void {
    \\        self.refs += 1;
    \\    }
    \\};
    \\
    \\const Node = struct {
    \\    bytes: []u8,
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator, other_ref: *OtherRef) void {
    \\        gpa.free(self.bytes);
    \\        self.finishOther(gpa, other_ref);
    \\    }
    \\
    \\    fn finishOther(self: *Node, gpa: std.mem.Allocator, other_ref: *OtherRef) void {
    \\        gpa.free(other_ref.bytes);
    \\        gpa.destroy(other_ref);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    gpa: std.mem.Allocator,
    \\    other_ref: *OtherRef,
    \\    node: *Node,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.node.free(self.gpa, self.other_ref);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a forwarded argument with no lifecycle call of its own is still charged" {
    // The declaration hands `other_ref` back through a path this rule
    // cannot follow, which leaves it charged and nothing to balance the
    // copy with.  The receiver's own free is evidence about `.node` and
    // no verdict at all on this side, and the allocator the call was
    // handed is not in this literal.
    const src = forwarded_argument_without_evidence ++
        \\pub fn copy(source: Holder) Holder {
        \\    return .{ .other_ref = source.other_ref };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.other_ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") == null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

/// Two ANONYMOUS literals, written the same way, constructing two
/// different declarations: what each one constructs is the type its
/// function returns, and that is the only thing that tells them apart.
/// `data` has a lifecycle in this file either way, so the quiet verdict
/// below is `View`'s own doing and not an absence of evidence.
const anonymous_return_pair =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    refs: *usize,
    \\
    \\    pub fn retain(self: *const Snapshot) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        if (self.refs.* == 0) gpa.free(self.refs);
    \\    }
    \\};
    \\
    \\/// Owns the snapshot: `deinit` gives the reference back.
    \\const Plan = struct {
    \\    data: *const Snapshot,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn deinit(self: *Plan) void {
    \\        self.data.release(self.gpa);
    \\    }
    \\};
    \\
    \\/// Borrows it: no destructor, so dropping a view decrements nothing.
    \\const View = struct {
    \\    data: *const Snapshot,
    \\};
    \\
    \\pub fn duplicate(other: Plan) Plan {
    \\    return .{ .data = other.data, .gpa = other.gpa };
    \\}
    \\
    \\pub fn borrow(doc: Plan) View {
    \\    return .{ .data = doc.data };
    \\}
    \\
;

test "ref-counted-copy-without-dupe: an anonymous literal is judged by the type its function returns" {
    // One file, one field spelling, two literals, two destinations:
    // `Plan` releases the snapshot and `View` only borrows it.  Exactly
    // one report is raised and it is the `Plan` copy — the `View` copy,
    // one line away, is silent.
    var problems = try testing.runRuleTyped(std.testing.allocator, check, anonymous_return_pair);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "other.data") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "doc.data") == null);
}

/// The teardown takes the field apart ITSELF, so nothing ever consults
/// a count on it: two handles each destroy one pointer and the second
/// is a double free whatever `retain` said in between.  The acquire is
/// written where this rule reads one — on the copy's own source and
/// field, the statement right before the copy — and it is still no fix.
const raw_destroy_literal_owner =
    \\const std = @import("std");
    \\
    \\const Entry = struct {
    \\    refs: u32 = 1,
    \\    bytes: []u8,
    \\
    \\    pub fn retain(self: *Entry) void {
    \\        self.refs += 1;
    \\    }
    \\};
    \\
    \\const Registry = struct {
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn destroy(self: *Registry, entry: *Entry) void {
    \\        self.gpa.destroy(entry);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    name: *Entry,
    \\    registry: *Registry,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.registry.destroy(self.name);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: an acquire cannot silence a literal copy the callee destroys outright" {
    // `Registry.destroy` hands the entry it is passed to its own
    // allocator, so two `Holder`s each destroy one pointer and the
    // second frees storage the first still owns.  `source.name.retain()`
    // is on the right source and the right field and really is called
    // before the copy — and nothing ever reads what `Entry.retain`
    // counts, so it balances nothing.
    const src = raw_destroy_literal_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    source.name.retain();
        \\    return Holder{ .name = source.name, .registry = source.registry };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    // Both fields this literal duplicates are handed back — the entry
    // `Registry.destroy` takes apart and the registry that call is made
    // on — so both are second owners and both are reported.
    try std.testing.expectEqual(@as(usize, 2), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[1].message, "`.registry`") != null);
}

/// The counterpart, and the reason the acquire is read on the copy's
/// own body rather than a few tokens back: here the declaration drives
/// the field through its own reference protocol, so one second reference
/// really is what the copy needs — and it is written some statements
/// ahead of the copy, not immediately before it.
const distant_protocol_owner =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    refs: *usize,
    \\    bytes: []const u8,
    \\
    \\    pub fn retain(self: *const Snapshot) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        if (self.refs.* == 0) gpa.free(self.bytes);
    \\    }
    \\};
    \\
    \\const Shared = struct {
    \\    gpa: std.mem.Allocator,
    \\    ref: *Snapshot,
    \\
    \\    pub fn deinit(self: *Shared) void {
    \\        self.ref.release(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: an acquire written well before the copy still balances it" {
    // `Shared.deinit` releases what `ref` holds, so the field's own
    // count decides when the storage goes and one acquire is the whole
    // fix.  It is written on the copy's own source and field, in the
    // copy's own body, and it runs before the copy — the three
    // statements between them are the only thing a fixed token window
    // would have stopped at.
    const src = distant_protocol_owner ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.ref.retain();
        \\    _ = source.gpa;
        \\    _ = source.gpa;
        \\    _ = source.gpa;
        \\    return Shared{ .ref = source.ref, .gpa = source.gpa };
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: an acquire cannot silence a literal copy whose teardown cannot be read" {
    // The acquire here is one this rule reads as one wherever it is
    // written: `kept` is an immutable local bound from exactly
    // `source.other_ref`, and `kept.retain()` is the statement right
    // after it.  It balances nothing all the same, because what `Holder`
    // does with that field is hand it to a callee whose body this rule
    // cannot follow to a verdict — and it is written through a local so
    // that the file never spells a lifecycle call on the field's own
    // name either.
    const src = forwarded_argument_without_evidence ++
        \\pub fn copy(source: Holder) Holder {
        \\    const kept = source.other_ref;
        \\    kept.retain();
        \\    return .{ .other_ref = source.other_ref };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.other_ref`") != null);
}

test "ref-counted-copy-without-dupe: a deferred acquire does not balance a literal copy either" {
    // The declaration drives `ref` through its own protocol, so an
    // acquire is the fix — but this one is deferred over a condition of
    // its own: it runs when the scope exits, after the copy it was
    // written for, and only if `keep` is true at all.  Reading the whole
    // body ahead of the copy must not turn that into a balance.
    const src = distant_protocol_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    defer if (keep) source.ref.retain();
        \\    return Shared{ .ref = source.ref, .gpa = source.gpa };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: an acquire written after the literal copy does not balance it" {
    // The same declaration and the same acquire, moved below the copy.
    // The copy already made the second owner by the time the reference
    // is added, so this is a statement the copy can no longer reach —
    // the other end of the window the acquire is read over.
    const src = distant_protocol_owner ++
        \\pub fn copy(source: Shared) Shared {
        \\    const copied = Shared{ .ref = source.ref, .gpa = source.gpa };
        \\    source.ref.retain();
        \\    return copied;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: the reported method is the one that hands the field back" {
    // Both references are released through a call spelled `.deref(...)`,
    // but the method that hands `tail` back is `Shared.drop`, and that
    // is the method a reader has to open.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    source.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`Shared.drop`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`Shared.deref`") == null);
}

test "ref-counted-copy-without-dupe: a wrapper handle is balanced by an acquire on the resource it holds" {
    // `Doc.deinit` does nothing but hand back `doc.ref`, so that
    // reference is the one `Shared.deref` releases through the wrapper —
    // and acquiring it is what balances the copy.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\/// A wrapper: nothing of its own, one reference it holds.
        \\const Doc = struct {
        \\    ref: *Snapshot,
        \\
        \\    pub fn deinit(self: *Doc, gpa: std.mem.Allocator) void {
        \\        self.ref.deref(gpa);
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    doc: *Doc,
        \\
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        self.doc.deinit(gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    source.doc.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: a wrapper that also stores borrowed metadata is still one reference" {
    // `Doc` hands back `ref` and nothing else.  The allocator it borrows
    // and the label it copies are fields it DECLARES, not references it
    // releases: no method of it touches either, so the one reference the
    // copy duplicates is the one `source.doc.ref.retain()` acquires.
    // A proof that read the wrapper's field list instead of its body
    // would call those two extra fields resources and report a copy
    // that is already fixed.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\/// A wrapper around `ref` that also carries borrowed metadata.
        \\const Doc = struct {
        \\    ref: *Snapshot,
        \\    gpa: std.mem.Allocator,
        \\    label: []const u8,
        \\
        \\    pub fn deinit(self: *Doc, gpa: std.mem.Allocator) void {
        \\        self.ref.deref(self.gpa);
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    doc: *Doc,
        \\
        \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        \\        self.doc.deinit(gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    source.doc.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: a nested resource of its own does not balance the handle" {
    // `Snapshot.deref` frees `self.bytes` and destroys `self`, so the
    // snapshot is a reference in its own right and `Snapshot.ref` is a
    // second one.  Retaining that second reference leaves the handle
    // duplicated, so the copy stays reported.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    bytes: []u8,
        \\    refcount: u64 = 1,
        \\    ref: ?*Snapshot = null,
        \\
        \\    pub fn retain(self: *Snapshot) void {
        \\        self.refcount += 1;
        \\    }
        \\
        \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refcount -= 1;
        \\        if (self.refcount == 0) {
        \\            gpa.free(self.bytes);
        \\            gpa.destroy(self);
        \\        }
        \\    }
        \\};
        \\
        \\const Handle = struct {
        \\    handle: *Snapshot,
        \\
        \\    pub fn deref(self: *Handle, gpa: std.mem.Allocator) void {
        \\        self.handle.deref(gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Handle) Handle {
        \\    source.handle.ref.?.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.handle`") != null);
}

// ── Which side of a cleanup call the payload is on ────────────────
//
// A teardown that hands storage back says so through a call, and the
// field a whole-value copy duplicates is whichever side of that call
// the payload is written on.  The payload is the callee's to declare,
// not the spelling's: an allocator field a call is MADE on is the
// mechanism that frees what it is HANDED, and a field HANDED to a
// callee that frees its own receiver is a borrowed argument.  No name
// decides either — the same `free`/`destroy` spelling on both sides of
// the call, in two declarations that differ only in what their callee's
// body does.

/// `Owner.deinit` frees `name` THROUGH the allocator field, so `gpa`
/// is the mechanism and `name` the payload.  The allocator is declared
/// FIRST on purpose: a verdict that reads the declaration order, or one
/// that believes every field heading a `destroy` is destroyed by it,
/// names the wrong field.
const allocator_first_owner =
    \\const std = @import("std");
    \\
    \\const OwnedName = struct {
    \\    refs: *usize,
    \\    text: []const u8,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn retain(self: *const OwnedName) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn deinit(self: *OwnedName) void {
    \\        self.refs.* -= 1;
    \\        self.gpa.free(self.text);
    \\    }
    \\};
    \\
    \\const Owner = struct {
    \\    gpa: std.mem.Allocator,
    \\    name: *OwnedName,
    \\
    \\    pub fn deinit(self: *Owner) void {
    \\        self.gpa.destroy(self.name);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a whole copy reports the destroyed pointee, not the allocator it is destroyed with" {
    // `Owner.deinit` calls `destroy` ON `self.gpa` and passes
    // `self.name`: the allocator is the mechanism that frees the
    // reference, and the reference is what the copy duplicates.  With
    // `gpa` declared first, a verdict that credits the field a handoff
    // is made on reports `.gpa` — and demands an acquire of a field the
    // declaration never gives back.
    const src = allocator_first_owner ++
        \\pub fn copy(source: Owner) Owner {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

test "ref-counted-copy-without-dupe: an acquire does not balance a descriptor this teardown destroys outright" {
    // This is the UNSAFE control for the fixture above, and the oracle
    // is the point: `Owner.deinit` destroys the descriptor itself, so
    // nothing ever consults what `OwnedName.retain` counts — the
    // teardown that would have decremented it is never called.  Two
    // `Owner`s each destroy one pointer and the second is a double
    // free, whatever the count said in between.
    //
    // An acquire balances a copy only where the declaration drives the
    // field through a reference protocol of its own.  A field handed to
    // something that frees it outright is destroyed whatever any count
    // says, so reading `retain` as a fix here would silence a real
    // double free — and the allocator is still only the mechanism, so
    // nothing asks for an acquire on it either.
    const src = allocator_first_owner ++
        \\pub fn copy(source: Owner) Owner {
        \\    source.name.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

/// The SAFE sibling of `allocator_first_owner`: the same
/// destroy-through-an-allocator call one level down, but the count that
/// decides it is the snapshot's own and the snapshot owns heap bytes.
/// `deref` decrements and frees at zero, so a second owner is a second
/// count rather than a second destroy — which is the whole difference
/// between a copy that needs an acquire and one that cannot be fixed
/// with one.
const protocol_release_owner =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    refs: u32 = 1,
    \\    bytes: []u8,
    \\
    \\    pub fn retain(self: *Snapshot) void {
    \\        self.refs += 1;
    \\    }
    \\
    \\    pub fn deref(self: *Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refs -= 1;
    \\        if (self.refs == 0) {
    \\            gpa.free(self.bytes);
    \\            gpa.destroy(self);
    \\        }
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    gpa: std.mem.Allocator,
    \\    name: *Snapshot,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.name.deref(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a handle that releases through a reference protocol is balanced by an acquire" {
    // The counterpart of the control above, and it differs from it in
    // one place only: `Holder.deinit` drives `name` through
    // `Snapshot.deref`, whose own count decides when the storage goes.
    // `source.name.retain()` acquires the second owner the copy
    // creates, so nothing is missing and nothing is reported — and
    // `gpa` is still only the mechanism, so no acquire is asked for on
    // the field the copy hands over as an argument.
    const src = protocol_release_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    source.name.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

/// A `free` this file DECLARES: `Node.free` hands its own receiver's
/// storage back, so `Holder.deinit` really does give `node` up through
/// it, and the allocator handed to that call is a borrowed argument.
/// Same spelling as the call above, opposite side carrying the payload.
const receiver_free_owner =
    \\const std = @import("std");
    \\
    \\const Node = struct {
    \\    refs: *usize,
    \\    text: []const u8,
    \\
    \\    pub fn retain(self: *const Node) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        gpa.free(self.text);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    gpa: std.mem.Allocator,
    \\    node: *Node,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.node.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a callee that frees its own receiver owns the field the call is made on" {
    // `free` is declared in this file, on `Node`, and its body frees
    // `self.text` — so the teardown owns `node` and borrows `gpa`.  The
    // copy duplicates `node`, which nothing acquired, and it is `node`
    // the finding names.
    const src = receiver_free_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

test "ref-counted-copy-without-dupe: an allocator spelled through an alias still frees its argument, not itself" {
    // The head's type is written `mem.Allocator` behind a local alias
    // and the field is called `arena`, so nothing here can be settled by
    // a field-name prefix: `arena` is the mechanism that frees what it
    // is handed, and `name` is the reference the handle owns.  A reader
    // that took the name of the field for the name of its type reports
    // `.arena` and asks for an acquire of a field this declaration
    // never gives back.
    const src =
        \\const std = @import("std");
        \\const mem = std.mem;
        \\
        \\const Descriptor = struct {
        \\    bytes: []const u8,
        \\};
        \\
        \\const Owner = struct {
        \\    arena: mem.Allocator,
        \\    name: *Descriptor,
        \\
        \\    pub fn deinit(self: *Owner) void {
        \\        self.arena.destroy(self.name);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Owner) Owner {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.arena`") == null);
}

/// `Alias` is a local alias of `Node`, so the head's declared type is
/// written `*Alias` and the declaration that decides the side is only
/// reached THROUGH it.
const aliased_receiver_owner =
    \\const std = @import("std");
    \\
    \\const Node = struct {
    \\    refs: *usize,
    \\    text: []const u8,
    \\
    \\    pub fn retain(self: *const Node) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        gpa.free(self.text);
    \\    }
    \\};
    \\
    \\const Alias = Node;
    \\
    \\const Holder = struct {
    \\    gpa: std.mem.Allocator,
    \\    node: *Alias,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.node.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: an owning receiver reached through a local alias owns the head" {
    // `Alias` names the very declaration `Node` does, and `Node.free`
    // frees its own receiver: `node` is the payload and `gpa` is the
    // borrowed argument.  A reader that stopped at the alias found no
    // callee here at all, and read the allocator as the reference the
    // copy duplicates.
    const src = aliased_receiver_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

/// An owning receiver that frees more than one field of its own: the
/// nested resource goes with it, and the allocator handed to that call
/// is still only a borrowed argument.  `gpa` is declared FIRST so that
/// a verdict that credited it would name it.
const nested_receiver_owner =
    \\const std = @import("std");
    \\
    \\const Child = struct {
    \\    bytes: []u8,
    \\};
    \\
    \\const Node = struct {
    \\    refs: *usize,
    \\    text: []u8,
    \\    child: *Child,
    \\
    \\    pub fn retain(self: *const Node) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        gpa.free(self.text);
    \\        gpa.destroy(self.child);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    gpa: std.mem.Allocator,
    \\    node: *Node,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.node.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: an owning receiver that frees nested storage still leaves the allocator borrowed" {
    // `Node.free` frees `self.text` AND destroys `self.child`, so the
    // head is what the teardown owns however much of itself it hands
    // back.  The allocator it was handed is a borrowed argument, and
    // holding one is not holding a second owner of anything.
    const src = nested_receiver_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

/// A teardown this file CAN open and still cannot follow: `Node.free`
/// frees nothing itself — it hands the call to `Node.finish`, and
/// `finish` is what gives `self.bytes` back.  A reader that scans only
/// the method the call is made on sees no free at all, and reading
/// that absence as "the argument is the payload" declared the copied
/// owning pointer borrowed and named the copied allocator the
/// reference it duplicates.  `name` is declared BEFORE `gpa`, so a
/// reading that credited the argument would report `gpa` instead.
const forwarded_free_owner =
    \\const std = @import("std");
    \\
    \\const Node = struct {
    \\    bytes: []u8,
    \\
    \\    pub fn finish(self: *Node, gpa: std.mem.Allocator) void {
    \\        gpa.free(self.bytes);
    \\    }
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator) void {
    \\        self.finish(gpa);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    name: *Node,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.name.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a teardown forwarded to another method still charges the copied pointer" {
    // `Holder.deinit` really does give the node back — through
    // `Node.finish` — so the copy hands one owning pointer to a second
    // owner and nothing acquires it.  The finding names `.name`, and
    // the allocator the call was handed is still only the mechanism.
    const src = forwarded_free_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return .{ .name = source.name, .gpa = source.gpa };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

test "ref-counted-copy-without-dupe: a whole copy whose teardown is forwarded says it cannot read it" {
    // The same declaration read through the whole-value pass, where the
    // finding may name what balances the copy.  What the callee shows
    // here is not a teardown of either side it was given, so the
    // finding must not claim the reference is one the teardown takes
    // apart — that claim is the reading this disposition replaced.  It
    // stays charged either way; only the reason is unread.
    const src = forwarded_free_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "cannot read what the teardown does") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "that teardown takes") == null);
}

/// The receiver freed through a C callback the handle was built with:
/// `Node.free` is this file's own declaration, its body names no
/// handoff at all, and the node is still freed — by `closer`, whose
/// body lives in another library.  This is the case where a body with
/// no DIRECT free in it must not be read as proof that the argument is
/// what the call destroys.  Legal source: every declaration here
/// compiles and links.
const pointer_free_owner =
    \\const std = @import("std");
    \\
    \\const Node = struct {
    \\    bytes: []u8,
    \\    closer: *const fn ([*]u8, usize) callconv(.c) void,
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator) void {
    \\        _ = gpa;
    \\        self.closer(self.bytes.ptr, self.bytes.len);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    name: *Node,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.name.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a receiver freed through a callback the file cannot follow stays charged" {
    // `Node.free` really does give the node back — the C callback
    // releases the bytes and the node with them — but that free is not
    // written where a reader can see it.  A "no direct free in the top
    // method" reading would name `.gpa`, and the copied owning pointer
    // with it would be declared borrowed.
    const src = pointer_free_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return .{ .name = source.name, .gpa = source.gpa };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

/// A method this file DECLARES and does not define: an `extern fn`
/// carries no body here, so what it frees is not a thing this rule can
/// read.  The head's declared type resolves and the method is named, so
/// this is exactly where a "no free in the body" reading would have
/// declared the copied owning pointer borrowed.  A parser-robustness
/// control, like the callee that is not declared at all: `extern`
/// parameters cannot be ABI types, so this shape is source for the
/// analyser and not something to compile.
const extern_free_owner =
    \\const std = @import("std");
    \\
    \\const Node = struct {
    \\    bytes: []u8,
    \\
    \\    extern fn free(self: *Node, gpa: std.mem.Allocator) void;
    \\};
    \\
    \\const Holder = struct {
    \\    name: *Node,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.name.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a callee declared without a body keeps the receiver charged" {
    // Same reading, one step further from a body: the method resolves,
    // and there is nothing behind it to say which side of
    // `self.name.free(self.gpa)` is the payload.  Both sides stay
    // charged, and the finding names the field the copy duplicates.
    const src = extern_free_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return .{ .name = source.name, .gpa = source.gpa };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

/// The other side of the same question, with the callee's own body
/// answering it: `Registry.destroy` hands the value it is PASSED to
/// its own allocator, so the argument is what this teardown gives back
/// and the registry the call is made on is only the mechanism.  The
/// entry is passed FIRST, so the argument index and the parameter index
/// are the same thing here — a body that destroys a different
/// parameter proves nothing about this one.
const argument_payer_owner =
    \\const std = @import("std");
    \\
    \\const Entry = struct {
    \\    refs: u32 = 1,
    \\    bytes: []u8,
    \\
    \\    pub fn retain(self: *Entry) void {
    \\        self.refs += 1;
    \\    }
    \\
    \\    pub fn deref(self: *Entry, gpa: std.mem.Allocator) void {
    \\        self.refs -= 1;
    \\        if (self.refs == 0) {
    \\            gpa.free(self.bytes);
    \\            gpa.destroy(self);
    \\        }
    \\    }
    \\};
    \\
    \\const Registry = struct {
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn destroy(self: *Registry, entry: *Entry) void {
    \\        self.gpa.destroy(entry);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    name: *Entry,
    \\    registry: *Registry,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.registry.destroy(self.name);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a callee that destroys the value it is passed is proved from its own body" {
    // The mirror of the forwarded case, and the one proof that does
    // survive it: `Registry.destroy` writes `self.gpa.destroy(entry)`
    // in the method the call is made on, `entry` is the parameter the
    // caller's first argument lands on, and the finding therefore says
    // the teardown takes `.name` apart itself.  `registry` is declared
    // after `name`, and stays out of it: the registry is the mechanism.
    const src = argument_payer_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "that teardown takes `.name` apart itself") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "cannot read what the teardown does") == null);
}

test "ref-counted-copy-without-dupe: an acquire cannot silence a copy the callee destroys outright" {
    // The unsafe control for the fixture above.  Nothing ever consults
    // what `Entry.retain` counts — `Registry.destroy` takes the entry
    // apart itself — so two `Holder`s each destroy one pointer and the
    // second is a double free whatever the count said in between.  An
    // acquire is a fix only where the declaration drives the field
    // through a protocol of its own, and taking it as one here would
    // silence a real double free.
    const src = argument_payer_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    source.name.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
}

/// The same call with the callee handing its ARGUMENT on rather than
/// destroying it: `Registry.destroy` forwards `entry` to `finish`, so
/// the body this rule can read shows the argument going nowhere, and
/// shows nothing at all about the registry either.  That is no proof
/// that the head is borrowed — it is no proof at all, so the copy
/// stays charged and says so.
const forwarded_argument_owner =
    \\const std = @import("std");
    \\
    \\const Entry = struct {
    \\    refs: u32 = 1,
    \\    bytes: []u8,
    \\
    \\    pub fn retain(self: *Entry) void {
    \\        self.refs += 1;
    \\    }
    \\};
    \\
    \\const Registry = struct {
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn destroy(self: *Registry, entry: *Entry) void {
    \\        self.finish(entry);
    \\    }
    \\
    \\    fn finish(self: *Registry, entry: *Entry) void {
    \\        self.gpa.destroy(entry);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    name: *Entry,
    \\    registry: *Registry,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.registry.destroy(self.name);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a callee that forwards the value it is passed proves nothing" {
    // `finish` is where the entry goes, and `destroy` does not say so
    // in anything a reader may take as a verdict: the argument is not
    // provably destroyed and the receiver is not provably kept.  The
    // finding therefore names the field the copy duplicates and says
    // the teardown could not be read — over-reporting on the argument
    // side rather than quieting the receiver by a guess.
    const src = forwarded_argument_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "cannot read what the teardown does") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "that teardown takes") == null);
}

/// The cross-side case in the shape a real teardown has: `Node.free`
/// frees its OWN storage outright and hands `other_ref` on to
/// `finishOther`, which frees that reference's bytes and the descriptor
/// with them.  Both references do go back — through two different paths
/// — and only one of them is a path this rule can follow.  Letting the
/// head's own free answer for the argument written beside it is what
/// declared a forwarded owning pointer borrowed, so that argument is
/// charged instead.
///
/// `other_ref` is declared BEFORE `node` so the mistake would show in
/// the finding rather than pass silently: a verdict that read the
/// head's free as a verdict on both names `node` — the field it read,
/// not the field it quieted.
const forwarded_argument_beside_freed_receiver =
    \\const std = @import("std");
    \\
    \\const OtherRef = struct {
    \\    refs: u32 = 1,
    \\    bytes: []u8,
    \\
    \\    pub fn retain(self: *const OtherRef) void {
    \\        self.refs += 1;
    \\    }
    \\};
    \\
    \\const Node = struct {
    \\    bytes: []u8,
    \\
    \\    pub fn free(self: *Node, gpa: std.mem.Allocator, other_ref: *OtherRef) void {
    \\        gpa.free(self.bytes);
    \\        self.finishOther(gpa, other_ref);
    \\    }
    \\
    \\    fn finishOther(self: *Node, gpa: std.mem.Allocator, other_ref: *OtherRef) void {
    \\        gpa.free(other_ref.bytes);
    \\        gpa.destroy(other_ref);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    gpa: std.mem.Allocator,
    \\    other_ref: *OtherRef,
    \\    node: *Node,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.node.free(self.gpa, self.other_ref);
    \\    }
    \\};
    \\
    \\/// Sharing the reference with a caller that keeps it is the one
    \\/// place this file drives `other_ref` through a protocol of its
    \\/// own, which is what gives the spelling a lifecycle at all: a
    \\/// field this file never acquires or releases is a plain value to
    \\/// it.  `share` is a function of its own rather than a method of
    \\/// `Holder`, so it lends `Holder` no verdict — what `Holder`
    \\/// gives the reference back is still what `deinit` says.
    \\pub fn share(holder: *Holder) *OtherRef {
    \\    holder.other_ref.retain();
    \\    return holder.other_ref;
    \\}
    \\
;

test "ref-counted-copy-without-dupe: a receiver's own free settles nothing about the argument beside it" {
    // `Node.free` frees `self.bytes` in its own body and FORWARDS
    // `other_ref` to `finishOther`, which is where that reference goes
    // back.  The copy hands `other_ref` to a second owner and nothing
    // acquires it, so the finding names it — the receiver's free is
    // evidence about `.node` and is not a verdict on the argument
    // written beside it.
    const src = forwarded_argument_beside_freed_receiver ++
        \\pub fn copy(source: Holder) Holder {
        \\    return .{ .other_ref = source.other_ref };
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.other_ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") == null);
    // The allocator handed to the call is what the callee borrows, and
    // it is not in this literal at all.
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
}

test "ref-counted-copy-without-dupe: an acquire cannot silence a copy whose forwarded argument teardown is unread" {
    // The same declaration through the whole-value pass, with the
    // acquire written on the field the copy duplicates.  It does not
    // balance this copy: an acquire is the fix only where the
    // declaration drives the field through a protocol of its own, and
    // nothing in `Holder` does that — what `Holder` does with
    // `other_ref` is hand it to a callee whose body the rule cannot
    // follow to a verdict.  `gpa` is the borrowed capability beside it
    // and `node` is still the head that teardown owns, so neither is
    // the reference this copy duplicates.
    const src = forwarded_argument_beside_freed_receiver ++
        \\pub fn copy(source: Holder) Holder {
        \\    source.other_ref.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.other_ref`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "cannot read what the teardown does") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "that teardown takes") == null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") == null);
}

/// A `destroy` made THROUGH a pointer to the standard allocator frees
/// what it is handed and nothing else: `raw_gpa` auto-derefs to the very
/// same `Allocator` interface the value would, and the descriptor it
/// points at stays allocated.  So `name` is what this teardown gives
/// back, and the descriptor `raw_gpa` points at is charged only where a
/// handoff that really takes it apart is written.
///
/// `raw_gpa` is declared FIRST so the reading would be visible: a
/// verdict that charged the pointer for the type's name would name it
/// here and leave the side that IS destroyed unreported.
const pointer_allocator_owner =
    \\const std = @import("std");
    \\
    \\const Descriptor = struct {
    \\    bytes: []const u8,
    \\};
    \\
    \\const Owner = struct {
    \\    raw_gpa: *std.mem.Allocator,
    \\    name: *Descriptor,
    \\
    \\    pub fn deinit(self: *Owner) void {
    \\        self.raw_gpa.destroy(self.name);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a destroy through a pointer to the standard allocator frees the argument, not the descriptor" {
    // `self.raw_gpa.destroy(self.name)` auto-derefs to the standard
    // `destroy`, which takes `name` apart itself.  The descriptor
    // `raw_gpa` points at is never freed by that call, so nothing about
    // it is duplicated here and the finding belongs to `name` — the
    // side a second owner really would double free.
    const src = pointer_allocator_owner ++
        \\pub fn copy(source: Owner) Owner {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.raw_gpa`") == null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "that teardown takes `.name` apart itself") != null);
}

/// The other side of the same question, and the one where the pointer IS
/// the owned thing: the descriptor the handle holds is heap storage of
/// its own, and the handoff that takes it apart is written through the
/// allocator the handle was handed — not through the pointer at it.
/// A `destroy` made through `raw_gpa` frees `name` and leaves that
/// descriptor allocated, so reading the pointer as an owned field would
/// report `name` instead and miss the double free that is really there.
/// `raw_gpa` is declared before `name` so the finding follows the field
/// whose ownership is real.
const pointer_allocator_destroyed =
    \\const std = @import("std");
    \\
    \\const Descriptor = struct {
    \\    bytes: []const u8,
    \\};
    \\
    \\const Owner = struct {
    \\    gpa: std.mem.Allocator,
    \\    raw_gpa: *std.mem.Allocator,
    \\    name: *Descriptor,
    \\
    \\    pub fn deinit(self: *Owner) void {
    \\        self.raw_gpa.destroy(self.name);
    \\        self.gpa.destroy(self.raw_gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a heap allocator descriptor this handle owns is still given back" {
    // Both references do go back, through the two different paths the
    // teardown writes, and the copy duplicates each of them.  The
    // descriptor is named first because nothing but
    // `self.gpa.destroy(self.raw_gpa)` settles it: the call made
    // through `raw_gpa` frees its argument and never the descriptor it
    // points at.
    const src = pointer_allocator_destroyed ++
        \\pub fn copy(source: Owner) Owner {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.raw_gpa`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.name`") == null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "that teardown takes `.raw_gpa` apart itself") != null);
}

/// The allocator handed to a callee is a capability it BORROWS — but
/// only when the handle holds the value.  A handle that holds a POINTER
/// to an allocator holds a descriptor somebody allocated and may or may
/// not own, and nothing in the spelling settles that; what the callee
/// does with it has to be read, and this one forwards its argument, so
/// it proves nothing either way.
///
/// `gpa` is declared FIRST so the finding follows it: a reader that
/// exempted any field of allocator type would silence a pointer to
/// storage this declaration may well own.
const pointer_allocator_argument =
    \\const std = @import("std");
    \\
    \\const Node = struct {
    \\    bytes: []u8,
    \\
    \\    pub fn finish(self: *Node, gpa: *std.mem.Allocator) void {
    \\        gpa.free(self.bytes);
    \\    }
    \\
    \\    pub fn free(self: *Node, gpa: *std.mem.Allocator) void {
    \\        self.finish(gpa);
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    gpa: *std.mem.Allocator,
    \\    name: *Node,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.name.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a pointer to the allocator handed to a callee stays charged" {
    // The same shape as the borrowed-allocator control, with the
    // allocator behind a pointer: `Node.free` forwards its argument, so
    // what happens to `gpa` is not a thing this file says, and a
    // pointer at an allocator nobody proves this handle owns is not the
    // borrowed capability either.  `gpa` is declared before `name` so
    // the finding names it.
    const src = pointer_allocator_argument ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "cannot read what the teardown does") != null);
}

/// A head this file cannot open: `Opaque` declares no `free` at all,
/// and `node` is declared BEFORE `gpa` so that a reading which credited
/// the argument would report `gpa` instead.
const undeclared_callee_owner =
    \\const std = @import("std");
    \\
    \\const Opaque = struct {
    \\    refs: u32 = 1,
    \\
    \\    pub fn retain(self: *Opaque) void {
    \\        self.refs += 1;
    \\    }
    \\};
    \\
    \\const Holder = struct {
    \\    node: *Opaque,
    \\    gpa: std.mem.Allocator,
    \\
    \\    pub fn deinit(self: *Holder) void {
    \\        self.node.free(self.gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a callee this file does not declare keeps the receiver charged" {
    // `free` is not declared on `Opaque`, so which side of
    // `self.node.free(self.gpa)` carries the payload is not a thing
    // this file says.  Reading the unreadable as "the argument is the
    // payload" is what declared a copied owning pointer borrowed and
    // named the copied allocator the reference it duplicates; both
    // sides stay charged instead, and the field the call is MADE on is
    // the one the finding names.
    const src = undeclared_callee_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
}

test "ref-counted-copy-without-dupe: an acquire cannot silence a copy whose teardown cannot be read" {
    // The same declaration with the acquire written in.  It balances a
    // copy only where the declaration drives the field through a
    // reference protocol of its own, and this one hands the field to a
    // callee that is not declared anywhere it can reach: an acquire on
    // a field whose protocol has not been seen is no proof, and taking
    // it as one would declare the copied pointer borrowed.
    const src = undeclared_callee_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    source.node.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
}

/// One handle, one reference: `Shared.deref` gives back what `ref`
/// holds, so a copy of the whole handle duplicates exactly one thing.
const single_owner =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    refs: *usize,
    \\    bytes: []const u8,
    \\
    \\    pub fn retain(self: *const Snapshot) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn deref(self: *const Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        if (self.refs.* == 0) {
    \\            gpa.free(self.bytes);
    \\        }
    \\    }
    \\};
    \\
    \\const Shared = struct {
    \\    ref: *Snapshot,
    \\
    \\    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
    \\        self.ref.deref(gpa);
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a static allocator callback is not a field teardown" {
    // `fn free(bytes: []u8) void` has no receiver, so it is an
    // allocator interface callback: the buffer it frees belongs to
    // whoever allocated it, and it hands nothing of this type back.
    // It lends the handle no verdict in either direction — the
    // reference `Shared.deref` releases is still duplicated by a copy
    // that acquires nothing.
    const src = single_owner ++
        \\fn free(bytes: []u8) void {
        \\    _ = bytes;
        \\}
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

// ── The same callee, reached through an import ────────────────────
//
// The head of a handoff is often a type this file only NAMES:
// `node: node_mod.Node` is a dotted path, and the declaration that
// decides which side of `self.node.free(self.gpa)` carries the payload
// lives behind it.  A reader that resolves one path segment, or that
// gave up on a dotted name altogether, found no callee here and read
// the call as freeing its argument — the reading that credits the
// copied allocator and calls the copied owning pointer borrowed.
//
// Both files are real and are analysed through a project cache, which
// is the only way a relative `@import` is answerable at all.
test "ref-counted-copy-without-dupe: an owning receiver behind an import owns the head, and an import this run cannot resolve still charges it" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "node.zig", .data =
        \\const std = @import("std");
        \\
        \\pub const Node = struct {
        \\    refs: *usize,
        \\    text: []const u8,
        \\
        \\    pub fn retain(self: *const Node) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn free(self: *Node, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        gpa.free(self.text);
        \\    }
        \\};
        \\
    });
    // The same handle, spelled through an import that resolves and
    // through one that does not.  `gpa` is declared FIRST in the first
    // so that a reading which credited the argument would name it, and
    // `node` is declared FIRST in the second so that a reading which
    // called the unreadable head quiet would name `gpa` instead.
    try tmp.dir.writeFile(io, .{ .sub_path = "resolved.zig", .data =
        \\const std = @import("std");
        \\const node_mod = @import("node.zig");
        \\
        \\const Holder = struct {
        \\    gpa: std.mem.Allocator,
        \\    node: node_mod.Node,
        \\
        \\    pub fn deinit(self: *Holder) void {
        \\        self.node.free(self.gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "unresolved.zig", .data =
        \\const std = @import("std");
        \\const node_mod = @import("absent.zig");
        \\
        \\const Holder = struct {
        \\    node: node_mod.Node,
        \\    gpa: std.mem.Allocator,
        \\
        \\    pub fn deinit(self: *Holder) void {
        \\        self.node.free(self.gpa);
        \\    }
        \\};
        \\
        \\pub fn copy(source: Holder) Holder {
        \\    return source;
        \\}
        \\
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    var project = project_cache_mod.ProjectCache.init(gpa, io);
    defer project.deinit();
    const cases = .{ .{ "resolved.zig", "`.node`" }, .{ "unresolved.zig", "`.node`" } };
    inline for (cases) |case| {
        const path = try std.fs.path.join(gpa, &.{ directory, case[0] });
        defer gpa.free(path);
        // The bytes analysed are the bytes on disk: the import resolves
        // against this path, so the file has to be this file.
        const bytes = try std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(1 << 20));
        defer gpa.free(bytes);
        const src_z = try gpa.dupeSentinel(u8, bytes, 0);
        defer gpa.free(src_z);
        var tree = try Ast.parse(gpa, src_z, .zig);
        defer tree.deinit(gpa);
        if (tree.errors.len != 0) return error.InvalidSyntax;
        var cache = file_cache_mod.FileCache.init(gpa, &tree);
        defer cache.deinit();
        cache.setProject(&project, path);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        // Each finding owns its formatted message, so the list's storage
        // is not the only thing this test has to hand back.
        defer testing.freeProblems(gpa, &problems);
        try check(gpa, &tree, &cache, &config_mod.Default, &problems);
        try std.testing.expectEqual(@as(usize, 1), problems.items.len);
        try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
        try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, case[1]) != null);
        // The allocator handed to a `free` that frees its own receiver
        // is a borrowed argument, and in the file whose callee cannot
        // be read the field the call is MADE on is what the finding
        // names — not the allocator it is written on top of.
        try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.gpa`") == null);
    }
}

// ── How many bindings a teardown may take from a field ─────────────

/// Ten names taken from `node` in one body, nine of which drive
/// nothing: the tenth is the one that releases the reference.  A
/// reader that keeps a fixed number of derived names stops before the
/// tenth and never sees the teardown at all, which drops the field from
/// the copy's obligations entirely.
const many_derived_captures =
    \\const std = @import("std");
    \\
    \\const Snapshot = struct {
    \\    refs: *usize,
    \\    bytes: []const u8,
    \\
    \\    pub fn retain(self: *const Snapshot) void {
    \\        self.refs.* += 1;
    \\    }
    \\
    \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
    \\        self.refs.* -= 1;
    \\        gpa.free(self.bytes);
    \\    }
    \\};
    \\
    \\const Shared = struct {
    \\    node: ?*Snapshot,
    \\
    \\    pub fn teardown(self: *Shared, gpa: std.mem.Allocator) void {
    \\        if (self.node) |a1| {
    \\            _ = a1;
    \\        }
    \\        if (self.node) |a2| {
    \\            _ = a2;
    \\        }
    \\        if (self.node) |a3| {
    \\            _ = a3;
    \\        }
    \\        if (self.node) |a4| {
    \\            _ = a4;
    \\        }
    \\        if (self.node) |a5| {
    \\            _ = a5;
    \\        }
    \\        if (self.node) |a6| {
    \\            _ = a6;
    \\        }
    \\        if (self.node) |a7| {
    \\            _ = a7;
    \\        }
    \\        if (self.node) |a8| {
    \\            _ = a8;
    \\        }
    \\        if (self.node) |a9| {
    \\            _ = a9;
    \\        }
    \\        if (self.node) |last| {
    \\            last.release(gpa);
    \\        }
    \\    }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a teardown with ten derived captures is read to the last one" {
    // The tenth capture is what releases `node`, so `Shared` hands that
    // reference back and the copy duplicates it.  The nine captures
    // before it bind real names from the same field and drive nothing,
    // which is exactly the shape a bounded list of derived names drops
    // on the floor.
    const src = many_derived_captures ++
        \\pub fn copy(source: Shared) Shared {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
}

test "ref-counted-copy-without-dupe: a name reused by a later scope is read as that scope's binding" {
    // Both fields are captured as `held`, in sibling scopes, and only
    // the second one drives the protocol.  At the call the first
    // binding is out of scope, so the release is the capture of `node`
    // and not of `other` — a reader that matches names anywhere in the
    // method charges both fields for one release and reports the one
    // this teardown never gives back.
    const src =
        \\const std = @import("std");
        \\
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn retain(self: *const Snapshot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *const Snapshot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        gpa.free(self.bytes);
        \\    }
        \\};
        \\
        \\const Shared = struct {
        \\    other: ?*Snapshot,
        \\    node: ?*Snapshot,
        \\
        \\    pub fn teardown(self: *Shared, gpa: std.mem.Allocator) void {
        \\        if (self.other) |held| {
        \\            _ = held;
        \\        }
        \\        if (self.node) |held| {
        \\            held.release(gpa);
        \\        }
        \\    }
        \\};
        \\
        \\pub fn copy(source: Shared) Shared {
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.node`") != null);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.other`") == null);
}

// ── When a balancing acquire runs ─────────────────────────────────
//
// An acquire balances a copy only by running before it.  A `defer`
// runs when the scope exits instead — after the return it was written
// for — and whatever the `defer` is written over decides where that
// statement ends, not which token happens to precede the receiver.

test "ref-counted-copy-without-dupe: a deferred conditional acquire does not balance the copy" {
    // The acquire is on the copy's own source and field and it is
    // really called, but it is deferred over a condition of its own: it
    // runs when the scope exits, after the `return`, and only if `keep`
    // is true.  The token before the receiver is `)`, not `defer`, so
    // nothing about this statement can be read off the token that
    // precedes the call.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    defer if (keep) source.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: a deferred acquire in a block does not balance the copy either" {
    // The same statement behind a block: the acquire is written after
    // a `{` rather than after the `defer` keyword, and it still runs
    // when the scope exits rather than before the return.
    const src = single_owner ++
        \\pub fn copy(source: Shared) Shared {
        \\    defer {
        \\        source.ref.retain();
        \\    }
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: the same acquire written where it runs does balance the copy" {
    // The immediate spelling of the line above.  One reference is
    // acquired for the second owner the copy creates, before the copy,
    // so nothing is missing and nothing is reported.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    _ = keep;
        \\    source.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

// ── Reaching the copy: an acquire the copy can be reached without ─────
//
// The window an acquire is searched in is the whole enclosing body, and an
// acquire written INSIDE a branch is not a reference every owner holds.
// `if (keep) source.ref.retain();` adds one on the paths that take the
// branch and none on the rest, while the `return source;` below it copies
// the handle on all of them — so the second owner is created on the paths
// where nothing was acquired, and `Shared.deref` then gives one reference
// back twice.
//
// Every fixture below is the same protocol and the same acquire; only the
// branch it is written in moves.  The pairs are the whole contract: a copy
// the acquire cannot be reached without is reported, and a copy written in
// the acquire's own branch — or below an acquire written at the top of the
// body — stays quiet.

test "ref-counted-copy-without-dupe: an acquire inside an if does not balance the copy after it" {
    // `keep` is false on half the paths, and on those the copy hands a
    // second holder a reference nobody acquired.  Reading the acquire off
    // the token above the copy would call that a second owner the
    // parameter and the copy already agreed on.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    if (keep) source.ref.retain();
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: an acquire in the branch the copy is written in does balance it" {
    // The correlated shape, one acquire per path that makes the copy: each
    // arm's copy is reached only through its own acquire, so nothing is
    // missing — and neither arm's acquire answers for the other.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    if (keep) {
        \\        source.ref.retain();
        \\        return source;
        \\    } else {
        \\        source.ref.retain();
        \\        return source;
        \\    }
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: an acquire in one arm does not balance the copy in the other" {
    // The neighbour case, and the one a whole-body scan gets wrong in the
    // other direction: the arm that retains is silent, and the arm that
    // copies without acquiring is one finding of its own.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    if (keep) {
        \\        source.ref.retain();
        \\        return source;
        \\    } else {
        \\        return source;
        \\    }
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: an acquire at the top of the body reaches a copy written inside a later branch" {
    // The arm a copy is written in does not make the copy conditional: the
    // acquire above the `if` has already run on every path that reaches
    // either copy, so neither is missing its second reference.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    source.ref.retain();
        \\    if (keep) return source;
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: an acquire in a loop body does not balance the copy after the loop" {
    // The loop may run zero times, so the acquire may never have run by
    // the time the copy hands the handle on.  The continue clause is
    // written on purpose: taking the loop's `{ … }` for a balanced group
    // without stepping over `: (i += 1)` first would put the trailing copy
    // INSIDE the loop and silence it again.
    const src = single_owner ++
        \\pub fn copy(source: Shared, count: usize) Shared {
        \\    var i: usize = 0;
        \\    while (i < count) : (i += 1) {
        \\        source.ref.retain();
        \\    }
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: a copy inside the loop body is reached by that body's acquire" {
    // The same loop with the copy where the acquire is: every iteration
    // that returns has retained first.  The loop's own extent is the one
    // both of them are written inside.
    const src = single_owner ++
        \\pub fn copy(source: Shared, count: usize) Shared {
        \\    var i: usize = 0;
        \\    while (i < count) : (i += 1) {
        \\        source.ref.retain();
        \\        return source;
        \\    }
        \\    unreachable;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: an acquire in a for body does not balance the copy after the loop" {
    // A `for` over an empty slice runs its body no times at all, which is
    // the same missing acquire as the `while` above with another keyword
    // in front of it.
    const src = single_owner ++
        \\pub fn copy(source: Shared, items: []const u8) Shared {
        \\    for (items) |byte| {
        \\        _ = byte;
        \\        source.ref.retain();
        \\    }
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: an acquire in one switch prong does not balance the copy in the next" {
    // Exactly one prong runs, and it is not the one that retained.  Both
    // copies are on the same declaration and the same field; only the
    // prong each is written in differs.
    const src = single_owner ++
        \\pub fn copy(source: Shared, mode: u8) Shared {
        \\    switch (mode) {
        \\        0 => {
        \\            source.ref.retain();
        \\            return source;
        \\        },
        \\        else => return source,
        \\    }
        \\}
        \\
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.ref`") != null);
}

test "ref-counted-copy-without-dupe: a copy inside the prong that retained is quiet" {
    // The other half of the pair above: the copy written where the acquire
    // is, inside one prong of the same switch, has its second reference.
    const src = single_owner ++
        \\pub fn copy(source: Shared, mode: u8) Shared {
        \\    switch (mode) {
        \\        0 => {
        \\            source.ref.retain();
        \\            return source;
        \\        },
        \\        else => unreachable,
        \\    }
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: an acquire in a catch payload does not balance the copy after it" {
    // The payload runs on the error path only, and the copy below runs on
    // the success path — where the reference was handed back untouched.
    const src = single_owner ++
        \\fn read() error{OutOfMemory}!u32 {
        \\    return 1;
        \\}
        \\pub fn copy(source: Shared) Shared {
        \\    const n = read() catch {
        \\        source.ref.retain();
        \\        return source;
        \\    };
        \\    _ = n;
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: an acquire in an else-if arm does not balance the copy below it" {
    // The acquire is conditioned on a SECOND decision, made inside the
    // `else` of the first: with `extra` false the `if` falls straight
    // through to the copy with nothing acquired.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool, extra: bool) Shared {
        \\    if (!keep) {
        \\        unreachable;
        \\    } else if (extra) {
        \\        source.ref.retain();
        \\    }
        \\    return source;
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: an acquire in a plain block still reaches the copy" {
    // A block is not a branch: it has been written and left by the time the
    // copy runs, so the acquire inside it has run.  Reading every `{ … }`
    // as conditional would report copies this rule must leave alone.
    const src = single_owner ++
        \\pub fn copy(source: Shared) Shared {
        \\    {
        \\        source.ref.retain();
        \\    }
        \\    return source;
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

test "ref-counted-copy-without-dupe: a conditional acquire does not balance a literal copy either" {
    // The same missing acquire read through the struct literal: `Shared`
    // drives `ref` through its own protocol, so an acquire is what this
    // copy needs — one that ran on the paths the copy runs on.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    if (keep) source.ref.retain();
        \\    return Shared{ .ref = source.ref };
        \\}
        \\
    ;
    try testing.expectFiresTyped(check, R, src);
}

test "ref-counted-copy-without-dupe: a literal copy in the branch that acquired is quiet" {
    // One acquire per path that builds the literal, so each handle the
    // function hands back holds a reference of its own.
    const src = single_owner ++
        \\pub fn copy(source: Shared, keep: bool) Shared {
        \\    if (keep) {
        \\        source.ref.retain();
        \\        return Shared{ .ref = source.ref };
        \\    } else {
        \\        source.ref.retain();
        \\        return Shared{ .ref = source.ref };
        \\    }
        \\}
        \\
    ;
    try testing.expectNoFireTyped(check, src);
}

// ── The destination declaration, written through an import ─────────
//
// The declaration a literal constructs is often named through an
// import: `imported.Owner{ … }`, a local annotated `const o :
// imported.Owner = .{ … }`, a return type of `imported.View`.  Reading
// through imports for a BARE name only left every qualified path with no
// declaration at all, and the copy then stood or fell on the spelling of
// its field — a name this file evidences nowhere went unreported though
// the owner releases it, and a borrowed view was reported for a
// reference that was never going to be released.
//
// Both files are real and are analysed through a project cache, which is
// the only way a relative `@import` is answerable at all.
test "ref-counted-copy-without-dupe: an imported owner is charged and an imported borrowed view is quiet" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "shapes.zig", .data =
        \\const std = @import("std");
        \\
        \\pub const Slot = struct {
        \\    refs: *usize,
        \\    bytes: []const u8,
        \\
        \\    pub fn retain(self: *const Slot) void {
        \\        self.refs.* += 1;
        \\    }
        \\
        \\    pub fn release(self: *Slot, gpa: std.mem.Allocator) void {
        \\        self.refs.* -= 1;
        \\        if (self.refs.* == 0) gpa.free(self.bytes);
        \\    }
        \\};
        \\
        \\/// Holds the handle and GIVES IT BACK: `release` drives it
        \\/// through its own count, so a second owner is a second one.
        \\pub const Owner = struct {
        \\    slot: Slot,
        \\
        \\    pub fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        self.slot.release(gpa);
        \\    }
        \\};
        \\
        \\/// The same storage read as a borrow: a pointer this
        \\/// declaration releases by nobody, ever.
        \\pub const View = struct {
        \\    buf: *const u8,
        \\
        \\    pub fn first(self: *const View) u8 {
        \\        return self.buf.*;
        \\    }
        \\};
        \\
    });
    // `slot` is not a name this rule reads as refcounted and no call in
    // this file is written on it, so nothing but the imported
    // declaration can charge these copies.  `Owner` is also declared
    // HERE, holding its slot by pointer and releasing nothing: a reader
    // that answered `imported.Owner` from this file's own scope would
    // read both copies as borrowed views and say nothing.
    try tmp.dir.writeFile(io, .{ .sub_path = "owned.zig", .data =
        \\const imported = @import("shapes.zig");
        \\
        \\const Owner = struct {
        \\    slot: *const imported.Slot,
        \\};
        \\
        \\pub fn rebuild(source: imported.Owner) imported.Owner {
        \\    return imported.Owner{ .slot = source.slot };
        \\}
        \\
        \\pub fn renew(source: imported.Owner) imported.Owner {
        \\    return .{ .slot = source.slot };
        \\}
        \\
    });
    // The same copy into a view that releases nothing, in a file that
    // DOES give the field's own spelling a lifecycle of its own.  That
    // is what the coarse fallback reads, so a reader that reached the
    // copy through the spelling instead of the declaration would report
    // a reference that is never released.
    try tmp.dir.writeFile(io, .{ .sub_path = "borrowed.zig", .data =
        \\const std = @import("std");
        \\const imported = @import("shapes.zig");
        \\
        \\pub const Buffer = struct {
        \\    buf: std.ArrayList(u8),
        \\
        \\    pub fn deinit(self: *Buffer, gpa: std.mem.Allocator) void {
        \\        self.buf.deinit(gpa);
        \\    }
        \\};
        \\
        \\pub fn peek(source: *const imported.View) imported.View {
        \\    return imported.View{ .buf = source.buf };
        \\}
        \\
        \\pub fn widen(source: *const imported.View) imported.View {
        \\    return .{ .buf = source.buf };
        \\}
        \\
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    var project = project_cache_mod.ProjectCache.init(gpa, io);
    defer project.deinit();
    const cases = .{ .{ "owned.zig", @as(usize, 2) }, .{ "borrowed.zig", @as(usize, 0) } };
    inline for (cases) |case| {
        const path = try std.fs.path.join(gpa, &.{ directory, case[0] });
        defer gpa.free(path);
        // The bytes analysed are the bytes on disk: the import resolves
        // against this path, so the file has to be this file.
        const bytes = try std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(1 << 20));
        defer gpa.free(bytes);
        const src_z = try gpa.dupeSentinel(u8, bytes, 0);
        defer gpa.free(src_z);
        var tree = try Ast.parse(gpa, src_z, .zig);
        defer tree.deinit(gpa);
        if (tree.errors.len != 0) return error.InvalidSyntax;
        var cache = file_cache_mod.FileCache.init(gpa, &tree);
        defer cache.deinit();
        cache.setProject(&project, path);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        // Each finding owns its formatted message, so the list's storage
        // is not the only thing this test has to hand back.
        defer testing.freeProblems(gpa, &problems);
        try check(gpa, &tree, &cache, &config_mod.Default, &problems);
        try std.testing.expectEqual(case[1], problems.items.len);
        for (problems.items) |problem| {
            try std.testing.expectEqualStrings(R, problem.rule_id);
            try std.testing.expect(std.mem.indexOf(u8, problem.message, "`.slot`") != null);
        }
    }
}
