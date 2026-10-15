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
//! Detection uses two declaration-bound copy passes. Field spellings and
//! unrelated lifecycle calls supply no ownership evidence.
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
//!     it: the type the enclosing function returns, an annotated local,
//!     or the callee parameter an argument literal is passed to. The
//!     SOURCE's type is never a stand-in for the destination.
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
//!         to read: unknown ownership stays silent.
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
//!     Raw slices have no reference-acquire protocol or implicit local
//!     destructor. Report only a proved second teardown obligation: a
//!     source cleanup that runs on success, a later owning use, or
//!     overlapping error cleanups. Fresh locals and optional takes can
//!     hand their slices to one returned owner. A temporary header adds
//!     no owner unless its uses prove cleanup or publication. Incomplete
//!     helper effects, escaped aliases, and unknown outcomes are not
//!     evidence of duplicate ownership and stay silent.
//!
//!   Pass 3 — whole-value copies, bound to the SOURCE DECLARATION:
//!     The declaration identifies the fields with cleanup obligations,
//!     but Zig has no automatic parameter destructors. Returning a
//!     parameter, or binding it to a local that owns cleanup only on
//!     error before handing it on, can transfer the one reference.
//!     Scalar reads and complete read-only methods do not add an owner.
//!     A resolved SDK append mutates its existing header. A straight-line
//!     move body must replace the whole receiver with proved fresh defaults,
//!     or disarm every returned owning field; its method name proves nothing.
//!     Distinct terminal returns, including an `orelse return` followed by
//!     one transfer on the present-value path, are exclusive handoffs.
//!     Additional aliases and unread mutation remain unknown and silent.
//!     Error-only cleanup overlaps a proved owning publication when a
//!     later failure can reach it. Unconditional cleanup requires a proved
//!     disarm before handoff. Complete helper storage outcomes can prove
//!     another release regardless of method spelling. Uses are matched to
//!     exact lexical bindings. No type name or path supplies a proof.
//!     A local the frame just built has one owner either way, and
//!     `return <local>;` is a move rather than a duplication.
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
const reference_ownership = @import("../../model/reference_ownership.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const std_type_query = @import("../../model/std_type_query.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ref-counted-copy-without-dupe";

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
    /// No destination or field ownership can be proved. Unknown stays silent;
    /// unrelated lifecycle calls and name resemblance prove no destructor.
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
    cache: *file_cache_mod.FileCache,
};

/// Admit the AST's byte, token-count, and node-count domains before any
/// bounded index walk. Counts stay counts until this checked conversion.
fn admittedTokenCount(source_len: usize, token_count: usize, node_count: usize) error{SourceTooWide}!Ast.TokenIndex {
    if (source_len >= std.math.maxInt(u32) or node_count > std.math.maxInt(u32))
        return error.SourceTooWide;
    return std.math.cast(Ast.TokenIndex, token_count) orelse error.SourceTooWide;
}

fn admitSource(tree: *const Ast) error{SourceTooWide}!Ast.TokenIndex {
    return admittedTokenCount(tree.source.len, tree.tokens.len, tree.nodes.len);
}

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ref_counted_copy_without_dupe)) return;
    const token_count = try admitSource(tree);
    if (token_count == 0) return;
    // All later root-model questions borrow this admitted model; a failed
    // build is an analysis error, never missing ownership evidence.
    _ = try cache.fileModel();

    var state = CheckState{ .problems = problems, .cache = cache };

    // ── Pass 3: whole-value copies ──────────────────────────────────────
    // Its evidence is the SOURCE declaration and never a field spelling,
    // so it stands on its own and is read first.
    try checkWholeValueCopies(gpa, tree, &state);

    // Struct-literal fields require a declaration-owned cleanup obligation.
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
/// Fields are read in declaration order; one copy reports the first remaining
/// obligation. Canonical acquisition and release queries share one work budget.
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
) !?OwnedRef {
    var evidence: reference_ownership.Query = .{};
    for (dest.info.fields) |*field| {
        if (try isBorrowedAllocatorValue(cache, dest.tree, dest.info, field.name)) continue;
        const teardown = (try lifecycleMethodOnField(cache, dest.tree, dest.info, field.name)) orelse continue;
        if (teardown.payload == .borrowed_argument) continue;
        // An acquire balances a copy ONLY when this declaration drives
        // the field through the field's own reference protocol.  A
        // teardown that hands the field's storage to an allocator takes
        // the field apart itself, so a count the second owner would
        // have kept on it is not what decides the second teardown — and
        // a callee this rule cannot read is no proof that the protocol
        // it has not seen is there.
        if (teardown.payload == .protocol) {
            const protocol: reference_ownership.ReleaseProtocol = .{
                .tree = dest.tree,
                .declaration = dest.info.findMethod(teardown.method).?.fn_decl,
                .field = field.name,
            };
            // The acquire has to reach THIS field on THIS source: one on
            // another field, receiver or subpath duplicates nothing here.
            if (try hasCanonicalAcquireCall(&evidence, cache, proto, body, tree, tags, body_first, copy_tok, source, field.name, protocol)) continue;
            if (try leafRefOfField(cache, dest, field)) |leaf| {
                const path = try std.fmt.allocPrint(cache.gpa, "{s}.{s}", .{ field.name, leaf });
                defer cache.gpa.free(path);
                var leaf_protocol = protocol;
                leaf_protocol.field = path;
                if (try hasCanonicalAcquireCall(&evidence, cache, proto, body, tree, tags, body_first, copy_tok, source, path, leaf_protocol)) continue;
            }
        }
        return .{ .field = field.name, .method = teardown.method, .payload = teardown.payload };
    }
    return null;
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
) !?[]const u8 {
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
            if ((try methodReachesField(cache, pointee.tree, pointee.info, m, receiver.name, member.name)) == null) continue;
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
        // Zig does not run a parameter destructor. A sole use transfers
        // ownership, unless the local copy is itself cleaned twice or
        // cleaned on success while it is also handed to another owner.
        if (try wholeCopyIsHandoff(state.cache, dest, tree, tags, t, source_tok, body_first, body_last, name) != false) continue;
        // The fix for a whole-value copy is an acquire that reaches
        // EVERY field the copy duplicates: `source.ref.retain();` and
        // `source.tail.retain();` before the return balance one second
        // owner each.  Only an acquire WRITTEN BEFORE the copy can
        // balance it, so the scan ends at the copy — one that runs
        // afterwards is a statement the copy can no longer reach.
        const unacquired = try unacquiredOwnedRef(
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

/// True proves one handoff; false proves overlapping cleanup/publication.
/// Null retains incomplete ownership evidence without reporting a duplicate.
fn wholeCopyIsHandoff(
    cache: *file_cache_mod.FileCache,
    owner: DestType,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    copy_start: Ast.TokenIndex,
    source_tok: Ast.TokenIndex,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    source: []const u8,
) !?bool {
    const fn_decl = tokens.enclosingFnDecl(tree, source_tok) orelse return null;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, fn_decl) orelse return null;
    const body = tokens.bodyOf(tree, fn_decl) orelse return null;
    const bindings = (try cache.localBindings(proto, body)).*;
    const source_binding = (bindings.findAt(source, source_tok) orelse return null).*;
    if (source_binding.origin != .param) return null;
    const returning = tags[copy_start] == .keyword_return;
    var source_unknown = false;
    var t = first;
    while (t <= last) : (t += 1) {
        if (t == source_tok or tags[t] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t), source)) continue;
        if (t > first and tags[t - 1] == .period) continue;
        const used = bindings.findAt(source, t) orelse continue;
        if (used.name_token != source_binding.name_token) continue;
        if (returning and wholeTerminalReturnUse(tree, source_tok, t, last, source)) continue;
        if (wholeUseReturnsBeforeCopy(tree, t, copy_start)) continue;
        if (wholeCopyTerminatesBeforeOtherUse(tree, source_tok, t)) continue;
        var member_end = t;
        while (member_end + 2 <= last and tags[member_end + 1] == .period and
            tags[member_end + 2] == .identifier) member_end += 2;
        if (member_end > t and (member_end + 1 > last or tags[member_end + 1] != .l_paren) and
            try sliceMemberIsScalar(cache, t, member_end))
        {
            t = member_end;
            continue;
        }
        if (try wholeUseCallsTeardown(cache, owner, tree, t, last)) return false;
        // Additional source uses are not themselves destructor obligations.
        // A known release/publication can prove overlap; an unread argument,
        // field update, or exclusive handoff only makes the result unknown.
        if (try wholeCallReleasesOwner(cache, tree, &bindings, source_binding, t) or
            try wholeCallPublishesOwner(cache, owner, tree, &bindings, source_binding, t) or
            try wholeReadOnlyCallReturnsOwner(cache, owner, tree, t)) return false;
        source_unknown = true;
    }
    if (returning) return if (source_unknown) null else true;
    const alias = tree.tokenSlice(copy_start + 1);
    const local = (bindings.findAt(alias, source_tok + 1) orelse return null).*;
    const local_last = @min(last, local.scope_close);
    var cleanups: usize = 0;
    var error_cleanups: usize = 0;
    var terminal_try_cleanup: ?Ast.TokenIndex = null;
    var unconditional_cleanup = false;
    var handoffs: usize = 0;
    var disarmed = false;
    var unknown = source_unknown;
    t = source_tok + 1;
    while (t <= local_last) : (t += 1) {
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), alias)) continue;
        // Member spellings do not refer to the local binding.
        if (t > first and tags[t - 1] == .period) continue;
        const used = bindings.findAt(alias, t) orelse continue;
        if (used.name_token != local.name_token) continue;
        if (t + 1 <= last and tags[t + 1] == .equal) {
            if (handoffs != 1) return null;
            if (fallibleAfterHandoff(tree, tags, source_tok, t - 1, alias)) return false;
            var frames: ReachFrames = .{};
            collectReachFrames(tags, first, local_last, &frames);
            if (!reachesCopy(&frames, t, local_last)) return if (disarmed) null else false;
            const reset_end = try freshHandleReset(cache, owner, tree, tags, t, local_last, alias) orelse return null;
            disarmed = true;
            t = reset_end;
            continue;
        }
        var end = t;
        while (end + 2 <= local_last and tags[end + 1] == .period and tags[end + 2] == .identifier)
            end += 2;
        if (end > t and end + 1 <= local_last and tags[end + 1] == .l_paren) {
            const close = tokens.matchParen(tags, end + 1, local_last) orelse return null;
            if (end == t + 2 and try wholeMethodDisarms(cache, owner, tree.tokenSlice(end))) {
                if (disarmed or deferredCall(tree, t)) return false;
                handoffs += 1;
                disarmed = true;
            } else if (isRefReleaseName(tree.tokenSlice(end)) or
                try wholeCallReleasesOwner(cache, tree, &bindings, local, t))
            {
                cleanups += 1;
                if (sliceDeferredAt(tree, t) == .error_only) {
                    error_cleanups += 1;
                } else if (t > first and tags[t - 1] == .keyword_try and
                    !hasFallibleTokensAfter(tree, close + 1, local_last))
                {
                    terminal_try_cleanup = t;
                }
                if (sliceDeferredAt(tree, t) != .error_only) unconditional_cleanup = true;
            } else if (try wholeCallPublishesOwner(cache, owner, tree, &bindings, local, t) or
                try wholeReadOnlyCallReturnsOwner(cache, owner, tree, t))
            {
                handoffs += 1;
            } else if (!try wholeCallBorrowsReceiver(cache, tree, t)) {
                unknown = true;
            }
            t = close;
        } else if (end > t and try sliceMemberIsScalar(cache, t, end)) {
            // A scalar value cannot carry another cleanup obligation.
            if (t > first and tags[t - 1] == .ampersand) return false;
            t = end;
        } else if (t > first and tags[t - 1] == .equal) {
            // A copied header is not a second destructor obligation by itself.
            unknown = true;
        } else if (t > first and tags[t - 1] == .keyword_return) {
            handoffs += 1;
        } else if (sliceCallContaining(tree, t)) |call_node| {
            // Passing an address does not create another owner. Only the
            // resolved body can prove a release, publication or owning loan.
            if (try wholeCallReleasesOwner(cache, tree, &bindings, local, t)) {
                cleanups += 1;
                if (sliceDeferredAt(tree, t) != .error_only) unconditional_cleanup = true;
            } else if (try wholeCallPublishesOwner(cache, owner, tree, &bindings, local, t) or
                try wholeReadOnlyCallReturnsOwner(cache, owner, tree, t))
            {
                handoffs += 1;
            } else {
                unknown = true;
            }
            t = tree.lastToken(call_node);
        } else {
            unknown = true;
        }
    }
    if (cleanups == 2 and error_cleanups == 1 and handoffs == 0) {
        if (terminal_try_cleanup) |release| {
            const overlap = (try wholeReleaseConsumesOnError(cache, tree, &bindings, local, release)) orelse return null;
            if (!overlap) return if (unknown) null else true;
        }
    }
    const disjoint = cleanups <= 1 and handoffs <= 1 and
        !(unconditional_cleanup and handoffs != 0 and !disarmed) and
        (cleanups == 0 or handoffs == 0 or disarmed or !fallibleAfterHandoff(tree, tags, source_tok, local_last, alias));
    if (!disjoint) return false;
    return if (unknown) null else true;
}

/// Match a cleanup to the owning declaration already read by the copy pass.
/// Parentheses may unwrap the same receiver; unrelated methods prove nothing.
fn wholeUseCallsTeardown(cache: *file_cache_mod.FileCache, owner: DestType, tree: *const Ast, use: Ast.TokenIndex, last: Ast.TokenIndex) !bool {
    const tags = tree.tokens.items(.tag);
    if (use + 5 <= last and tags[use + 1] == .period and
        tags[use + 2] == .identifier and tags[use + 3] == .period and
        tags[use + 4] == .identifier and tags[use + 5] == .l_paren)
    {
        if ((try verdictOnField(cache, owner, tree.tokenSlice(use + 2))) != .owned) return false;
        return isRefReleaseName(tree.tokenSlice(use + 4));
    }
    var after = use + 1;
    while (after <= last and tags[after] == .r_paren) : (after += 1) {}
    if (after + 2 > last or tags[after] != .period or
        tags[after + 1] != .identifier or tags[after + 2] != .l_paren) return false;
    for (owner.info.methods) |*method| {
        if (!std.mem.eql(u8, method.name, tree.tokenSlice(after + 1))) continue;
        const receiver = method.receiver orelse continue;
        for (owner.info.fields) |field| {
            if (try methodReachesField(cache, owner.tree, owner.info, method, receiver.name, field.name) != null) return true;
        }
    }
    return false;
}

fn hasFallibleTokensAfter(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    var token = first;
    while (token <= last) : (token += 1) {
        switch (tree.tokenTag(token)) {
            .keyword_try, .keyword_error => return true,
            else => {},
        }
    }
    return false;
}

/// Success consumes one entry payload; rollback sees that same payload only
/// when a complete error outcome says it was already consumed before failure.
/// An unread error effect remains unknown, not a retry-safety certificate.
fn wholeReleaseConsumesOnError(cache: *file_cache_mod.FileCache, tree: *const Ast, bindings: *const local_bindings.LocalBindings, local: local_bindings.Binding, use: Ast.TokenIndex) !?bool {
    const node = sliceCallContaining(tree, use) orelse return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return null;
    const token = @import("../../cache/fresh_storage.zig").calleeQueryToken(tree, call);
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return null;
    const summary = (try cache.summaryOfResolvedMethod(actual.callee)) orelse return null;
    if (!summary.normal_success_storage_effects_complete or !summary.error_storage_effects_complete) return null;
    if (try sliceCallReleaseCount(cache, tree, bindings, actual, summary.normal_success_storage_outcomes, local, null) != 1) return null;
    return try sliceCallReleaseCount(cache, tree, bindings, actual, summary.error_storage_outcomes, local, null) != 0;
}

/// A resolved, complete storage outcome can prove that a helper releases
/// the local's entry payload even when its name describes in-place work.
fn wholeCallReleasesOwner(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    local: local_bindings.Binding,
    use: Ast.TokenIndex,
) !bool {
    const node = sliceCallContaining(tree, use) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    const token = @import("../../cache/fresh_storage.zig").calleeQueryToken(tree, call);
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    if (try sliceAllocatorReleasesLocal(cache, tree, bindings, actual, local, null)) return true;
    const summary = (try cache.summaryOfResolvedMethod(actual.callee)) orelse return false;
    if (!summary.normal_success_storage_effects_complete) return false;
    return try sliceCallReleaseCount(cache, tree, bindings, actual, summary.normal_success_storage_outcomes, local, null) != 0;
}

/// Publishing a by-value handle into a receiver's owning field proves a
/// second cleanup obligation. The callee and both parameter bindings are
/// exact; a store into a borrowed field or an unread body proves nothing.
fn wholeCallPublishesOwner(
    cache: *file_cache_mod.FileCache,
    owner: DestType,
    caller_tree: *const Ast,
    caller_bindings: *const local_bindings.LocalBindings,
    local: local_bindings.Binding,
    use: Ast.TokenIndex,
) !bool {
    const node = sliceCallContaining(caller_tree, use) orelse return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = caller_tree.fullCall(&call_buffer, node) orelse return false;
    const token = @import("../../cache/fresh_storage.zig").calleeQueryToken(caller_tree, call);
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    const tree = actual.callee.tree;
    const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, actual.callee.declaration) orelse return false;
    const bindings = (try declaring.localBindings(proto, body)).*;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .assign) continue;
        const assignment: Ast.Node.Index = @enumFromInt(index);
        // A sole assignment cannot retract or replace the published owner
        // before success. More complex bodies need a retained-owner proof.
        if (tree.firstToken(assignment) != tree.firstToken(body) + 1 or
            tree.lastToken(assignment) + 2 != tree.lastToken(body)) continue;
        const pair = tree.nodeData(assignment).node_and_node;
        if (tree.nodeTag(pair[0]) != .field_access or tree.nodeTag(pair[1]) != .identifier) continue;
        const target = tree.nodeData(pair[0]).node_and_token;
        if (tree.nodeTag(target[0]) != .identifier) continue;
        const target_token = tree.nodeMainToken(target[0]);
        const source_token = tree.nodeMainToken(pair[1]);
        const source_binding = bindings.findAt(tree.tokenSlice(source_token), source_token) orelse continue;
        const target_binding = bindings.findAt(tree.tokenSlice(target_token), target_token) orelse continue;
        if (source_binding.origin != .param or target_binding.origin != .param) continue;
        const source_owner = paramHandleType(declaring, tree, proto, source_binding.name) orelse continue;
        if (source_owner.tree != owner.tree or source_owner.info.body_first != owner.info.body_first) continue;
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        var source_index: ?u32 = null;
        var destination: ?DestType = null;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            if (parameter.name_token == source_binding.name_token) source_index = parameter_index;
            if (parameter.name_token != target_binding.name_token) continue;
            const type_expr = parameter.type_expr orelse continue;
            // A local by-value parameter is not an externally live slot.
            const type_first = tree.firstToken(type_expr);
            if (tree.tokenTag(type_first) != .asterisk or
                tree.tokenTag(type_first + 1) == .keyword_const) continue;
            destination = declaredTypeDeclAt(declaring, tree, tree.firstToken(type_expr), tree.lastToken(type_expr));
        }
        const selected = source_index orelse continue;
        if (!try sliceCallNamesLocal(cache, caller_tree, caller_bindings, actual, .{
            .param = selected,
            .path = "",
        }, local, null)) continue;
        const dest = destination orelse continue;
        const field = dest.info.findField(tree.tokenSlice(target[1])) orelse continue;
        if (declaredPointer(dest.tree, field)) continue;
        const field_owner = bindTypeRange(declaring, dest.tree, field.type_first, field.type_last) orelse continue;
        if (field_owner.tree != owner.tree or field_owner.info.body_first != owner.info.body_first) continue;
        if ((try verdictOnField(declaring, dest, field.name)) == .owned) return true;
    }
    return false;
}

/// A copied local in a terminal branch cannot coexist with a later use
/// outside that branch. A break/continue refuses this proof.
fn wholeCopyTerminatesBeforeOtherUse(tree: *const Ast, copy: Ast.TokenIndex, other: Ast.TokenIndex) bool {
    if (other <= copy or deferredCall(tree, copy) or deferredCall(tree, other)) return false;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (copy < tree.firstToken(node) or copy > tree.lastToken(node) or other <= tree.lastToken(node)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&buffer, node) orelse continue;
        for (statements) |statement| {
            if (tree.nodeTag(statement) != .@"return" or tree.firstToken(statement) <= copy) continue;
            const tags = tree.tokens.items(.tag);
            if (tokens.hasTokenInRange(tags, copy, tree.firstToken(statement), .keyword_break) or
                tokens.hasTokenInRange(tags, copy, tree.firstToken(statement), .keyword_continue)) break;
            return true;
        }
    }
    return false;
}

/// A use within an earlier terminal return cannot coexist with this copy.
fn wholeUseReturnsBeforeCopy(tree: *const Ast, use: Ast.TokenIndex, copy: Ast.TokenIndex) bool {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.lastToken(node) >= copy) continue;
        if (tree.firstToken(node) <= use and use <= tree.lastToken(node)) return true;
    }
    return false;
}

/// Distinct non-deferred returns cannot execute on the same path. An
/// `orelse return` also excludes a sole later transfer, even when the
/// later call stores its result rather than returning it immediately.
fn wholeTerminalReturnUse(tree: *const Ast, copied: Ast.TokenIndex, other: Ast.TokenIndex, last: Ast.TokenIndex, source: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    if (deferredCall(tree, copied) or deferredCall(tree, other)) return false;
    var copied_return: ?Ast.Node.Index = null;
    var other_return: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, i| {
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(i);
        const start = tree.firstToken(node);
        const stop = tree.lastToken(node);
        if (copied >= start and copied <= stop) copied_return = node;
        if (other < start or other > stop) continue;
        var count: usize = 0;
        var t = start;
        while (t <= stop) : (t += 1) {
            if (tags[t] == .identifier and std.mem.eql(u8, tree.tokenSlice(t), source) and
                (t == start or tags[t - 1] != .period)) count += 1;
        }
        if (count != 1) return false;
        other_return = node;
    }
    if (other + 1 >= tags.len or
        (tags[other + 1] != .semicolon and tags[other + 1] != .comma and tags[other + 1] != .r_paren)) return false;
    const early = copied_return orelse return false;
    if (other_return) |later| return early != later;
    const start = tree.firstToken(early);
    const stop = tree.lastToken(early);
    if (start == 0 or tags[start - 1] != .keyword_orelse or other <= stop or
        (other > 0 and tags[other - 1] == .ampersand)) return false;
    var count: usize = 0;
    var t = stop + 1;
    while (t <= last) : (t += 1) {
        if (tags[t] == .identifier and std.mem.eql(u8, tree.tokenSlice(t), source) and
            tags[t - 1] != .period) count += 1;
    }
    return count == 1;
}

/// Prove a self-disarming operation from a complete, straight-line body.
/// The direct form copies the receiver, replaces it with independent storage,
/// then returns the copy. The aggregate form transfers every owning field
/// through another proved disarming operation; the remaining fields are scalar.
/// Recursive descents only follow by-value fields, never pointer cycles.
fn wholeMethodDisarms(cache: *file_cache_mod.FileCache, owner: DestType, name: []const u8) anyerror!bool {
    const tree = owner.tree;
    if (tree != cache.tree) return false;
    const tags = tree.tokens.items(.tag);
    const method = owner.info.findMethod(name) orelse return false;
    const receiver = method.receiver orelse return false;
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, method.fn_decl) orelse return false;
    const result_type = proto.ast.return_type.unwrap() orelse return false;
    const result_owner = bindTypeExpr(cache, tree, result_type) orelse return false;
    if (result_owner.info != owner.info) return false;
    var params = proto.iterate(tree);
    const recv_param = params.next() orelse return false;
    if (params.next() != null) return false;
    const recv_type = recv_param.type_expr orelse return false;
    const recv_first = tree.firstToken(recv_type);
    if (tags[recv_first] != .asterisk or tags[recv_first + 1] == .keyword_const) return false;
    var t = method.body_first + 1;
    const last = method.body_last;
    if (t + 16 == last and tags[t] == .keyword_const and tags[t + 1] == .identifier and
        tags[t + 2] == .equal and tags[t + 3] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(t + 3), receiver.name) and tags[t + 4] == .period_asterisk and
        tags[t + 5] == .semicolon and tags[t + 6] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(t + 6), receiver.name) and tags[t + 7] == .period_asterisk and
        tags[t + 8] == .equal and tags[t + 9] == .period and tags[t + 10] == .l_brace and
        tags[t + 11] == .r_brace and tags[t + 12] == .semicolon and tags[t + 13] == .keyword_return and
        tags[t + 14] == .identifier and std.mem.eql(u8, tree.tokenSlice(t + 14), tree.tokenSlice(t + 1)) and
        tags[t + 15] == .semicolon)
    {
        return try cache.provesFreshStorage(.{
            .first = t + 9,
            .last = t + 11,
            .type_first = tree.firstToken(result_type),
            .type_last = tree.lastToken(result_type),
        }, null);
    }
    const captures_first = t;
    while (t + 12 < last and tags[t] == .keyword_const) {
        if (tags[t + 1] != .identifier or tags[t + 2] != .equal or
            tags[t + 5] != .identifier or tags[t + 6] != .semicolon or
            !isRecvFieldAt(tree, tags, t + 3, last, receiver.name, tree.tokenSlice(t + 5)) or
            !isRecvFieldAt(tree, tags, t + 7, last, receiver.name, tree.tokenSlice(t + 5)) or
            tags[t + 10] != .equal or tags[t + 11] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 11), "null") or tags[t + 12] != .semicolon) return false;
        const field = owner.info.findField(tree.tokenSlice(t + 5)) orelse return false;
        if (tags[field.type_first] != .question_mark) return false;
        t += 13;
    }
    const captures_last = t;
    if (t + 3 > last or tags[t] != .keyword_return or tags[t + 1] != .period or
        tags[t + 2] != .l_brace) return false;
    t += 3;
    for (owner.info.fields) |field| {
        if (t + 3 > last or tags[t] != .period or tags[t + 1] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 1), field.name) or tags[t + 2] != .equal) return false;
        const value = t + 3;
        if (tags[value] == .identifier and value + 1 <= last and
            (tags[value + 1] == .comma or tags[value + 1] == .r_brace))
        {
            var capture = captures_first;
            while (capture < captures_last) : (capture += 13) {
                if (std.mem.eql(u8, tree.tokenSlice(capture + 1), tree.tokenSlice(value)) and
                    std.mem.eql(u8, tree.tokenSlice(capture + 5), field.name)) break;
            }
            if (capture == captures_last) return false;
            t = value + 1;
            if (tags[t] == .comma) t += 1 else if (tags[t] != .r_brace) return false;
            continue;
        }
        if (!isRecvFieldAt(tree, tags, value, last, receiver.name, field.name)) return false;
        t += 6;
        if (t + 3 <= last and tags[t] == .period and tags[t + 1] == .identifier and
            tags[t + 2] == .l_paren and tags[t + 3] == .r_paren)
        {
            if (tags[field.type_first] == .asterisk or tags[field.type_first] == .question_mark) return false;
            const nested = bindTypeRange(cache, tree, field.type_first, field.type_last) orelse return false;
            if (!try wholeMethodDisarms(cache, nested, tree.tokenSlice(t + 1))) return false;
            t += 4;
        } else if (!try sliceMemberIsScalar(cache, value, value + 2)) {
            return false;
        }
        if (tags[t] == .comma) t += 1 else if (tags[t] != .r_brace) return false;
    }
    return t + 2 == last and tags[t] == .r_brace and tags[t + 1] == .semicolon;
}

/// Complete read-only calls with pointer receivers and address-free results
/// cannot publish another owner. The resolved SDK append is also safe:
/// it updates its own header rather than returning or storing a second one.
fn wholeCallBorrowsReceiver(cache: *file_cache_mod.FileCache, tree: *const Ast, use: Ast.TokenIndex) !bool {
    const call_node = sliceCallContaining(tree, use) orelse return false;
    var call_buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, call_node) orelse return false;
    const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)) orelse return false;
    if (actual.argument_offset != 1) return false;
    const declared = (try actual.declaringCache(cache)) orelse return false;
    const resolver = declared.zls orelse return false;
    const frame = resolver.frameForFunction(actual.callee.reference);
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(actual.callee.tree, &proto_buf, actual.callee.declaration) orelse return false;
    var params = proto.iterate(actual.callee.tree);
    const receiver = params.next() orelse return false;
    const receiver_node = receiver.type_expr orelse return false;
    const receiver_type = (try frame.typeOfNode(receiver_node)) orelse return false;
    if (resolver.typeTag(receiver_type) != .pointer) return false;
    var return_node = proto.ast.return_type.unwrap() orelse return false;
    while (actual.callee.tree.nodeTag(return_node) == .error_union)
        return_node = actual.callee.tree.nodeData(return_node).node_and_node[1];
    const returned = (try frame.typeOfNode(return_node)) orelse return false;
    if (!try @import("../../cache/fresh_storage.zig").actualTypeAddressFree(frame, returned, 0, null)) return false;
    const caller = actual.callee.caller_frame orelse (cache.zls orelse return false).resolutionFrame();
    // The resolved SDK append updates its own owning header. Growth may
    // invalidate old element addresses, but does not publish a second header.
    if (try caller.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len) != .no) return true;
    // Mutation effects alone do not prove that a project method neither
    // retains nor frees storage. Require a complete whole-body read-only fact.
    return (try cache.callEffectAt(tree.nodeMainToken(call.ast.fn_expr), .{ .whole = actual.callee }, .{})) == .read_only;
}

/// A returned loan leaves the source alive. It creates a second cleanup
/// obligation only when the result's own uses prove cleanup or publication.
fn wholeReadOnlyCallReturnsOwner(
    cache: *file_cache_mod.FileCache,
    owner: DestType,
    tree: *const Ast,
    use: Ast.TokenIndex,
) !bool {
    const call_node = sliceCallContaining(tree, use) orelse return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, call_node) orelse return false;
    const token = @import("../../cache/fresh_storage.zig").calleeQueryToken(tree, call);
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(actual.callee.tree, &proto_buffer, actual.callee.declaration) orelse return false;
    var result = proto.ast.return_type.unwrap() orelse return false;
    while (actual.callee.tree.nodeTag(result) == .error_union)
        result = actual.callee.tree.nodeData(result).node_and_node[1];
    const destination = bindTypeExpr(declaring, actual.callee.tree, result) orelse return false;
    if (destination.tree != owner.tree or destination.info.body_first != owner.info.body_first) return false;
    if ((try cache.callEffectAt(token, .{ .whole = actual.callee }, .{})) != .read_only) return false;
    const storage = @import("../../cache/return_storage.zig");
    const returned = try storage.returnedStorageAt(cache, token, .{});
    if (!try wholeReturnedLoanIsOwned(cache, tree, call_node)) return false;
    for (returned.alternatives) |alternative| {
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const selected = (try storage.mappedStorageAt(cache, actual, alternative, &argument_buffer)) orelse continue;
        var argument = selected.node;
        while (true) {
            argument = switch (tree.nodeTag(argument)) {
                .identifier => {
                    if (tree.nodeMainToken(argument) == use) return true;
                    break;
                },
                .address_of => tree.nodeData(argument).node,
                .field_access, .grouped_expression, .unwrap_optional => tree.nodeData(argument).node_and_token[0],
                else => break,
            };
        }
    }
    return false;
}

fn wholeReturnedLoanIsOwned(cache: *file_cache_mod.FileCache, tree: *const Ast, call: Ast.Node.Index) !bool {
    const first = tree.firstToken(call);
    const last = tree.lastToken(call);
    const declaration = tokens.enclosingFnDecl(tree, first) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        if (tree.firstToken(value) <= first and tree.lastToken(value) >= last and
            tokens.enclosingFnDecl(tree, tree.firstToken(node)) == declaration) return true;
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    const bindings = (try cache.localBindings(proto, body)).*;
    for (bindings.items) |binding| {
        if (binding.origin == .param or binding.rhs_first > first or binding.rhs_last < last) continue;
        // Mere result existence, a discarded result, or an unread alias does
        // not add an owner. Reuse the copy pass's exact local-use evidence.
        if (try sliceBindingUsesAreDisjoint(cache, tree, &bindings, body, binding, null, null, false, false, null) == false) return true;
    }
    return false;
}

/// A pending error cleanup cannot follow a successful transfer across
/// another fallible operation unless the local's old payload is disarmed.
fn fallibleAfterHandoff(tree: *const Ast, tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, last: Ast.TokenIndex, alias: []const u8) bool {
    var transferred = false;
    var t = first + 1;
    while (t <= last) : (t += 1) {
        if (transferred and (tags[t] == .keyword_try or
            (tags[t] == .keyword_return and t + 1 <= last and tags[t + 1] == .keyword_error))) return true;
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), alias)) continue;
        if (t + 1 <= last and (tags[t + 1] == .comma or tags[t + 1] == .r_paren)) transferred = true;
    }
    return false;
}

/// Read the reset declaration, not the method's spelling. Only an
/// allocator capability may flow from the old handle into a fresh value.
fn freshHandleReset(cache: *file_cache_mod.FileCache, owner: DestType, tree: *const Ast, tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex, alias: []const u8) !?Ast.TokenIndex {
    var method_tok = start + 2;
    if (method_tok > last or tags[method_tok] != .identifier) return null;
    const type_first = method_tok;
    while (method_tok + 2 <= last and tags[method_tok + 1] == .period and tags[method_tok + 2] == .identifier)
        method_tok += 2;
    if (method_tok == type_first or method_tok + 6 > last or tags[method_tok + 1] != .l_paren) return null;
    const reset_type = bindTypeRange(cache, tree, type_first, method_tok - 2) orelse return null;
    if (reset_type.info != owner.info or reset_type.tree != owner.tree) return null;
    const arg = method_tok + 2;
    if (!isRecvFieldAt(tree, tags, arg, last, alias, tree.tokenSlice(arg + 2))) return null;
    if (tags[arg + 3] != .r_paren or tags[arg + 4] != .semicolon) return null;
    const capability = owner.info.findField(tree.tokenSlice(arg + 2)) orelse return null;
    if (!std_type_query.isType(cache, owner.tree, capability.type_first, capability.type_last, "mem", "Allocator", .{ .allow_pointer = false })) return null;
    if (!try allocatorFactory(cache, reset_type, tree.tokenSlice(method_tok), 0)) return null;
    return arg + 4;
}

/// A bounded declaration proof: one allocator parameter, one returned
/// literal, and only that capability or another proved constructor in
/// its fields. Captures, opaque methods and control flow stay unknown.
fn allocatorFactory(cache: *file_cache_mod.FileCache, owner: DestType, method_name: []const u8, depth: usize) !bool {
    if (depth == 16) return false;
    const tree = owner.tree;
    _ = try admitSource(tree);
    const tags = tree.tokens.items(.tag);
    const method = owner.info.findMethod(method_name) orelse return false;
    if (method.receiver != null) return false;
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, method.fn_decl) orelse return false;
    var params = proto.iterate(tree);
    const param = params.next() orelse return false;
    if (params.next() != null) return false;
    const param_name = tree.tokenSlice(param.name_token orelse return false);
    const param_type = param.type_expr orelse return false;
    if (!std_type_query.isType(cache, tree, tree.firstToken(param_type), tree.lastToken(param_type), "mem", "Allocator", .{ .allow_pointer = false })) return false;
    // Unknown defaults can retain an external owner rather than create
    // an empty container; they cannot prove this reset.
    for (owner.info.fields) |field| {
        if (!field.has_default) continue;
        const value = field.type_last + 2;
        switch (tags[value]) {
            .number_literal => {},
            .identifier => {
                const literal = tree.tokenSlice(value);
                if (!std.mem.eql(u8, literal, "null") and
                    !std.mem.eql(u8, literal, "true") and
                    !std.mem.eql(u8, literal, "false")) return false;
            },
            .period => if (tags[value + 1] != .identifier or !std.mem.eql(u8, tree.tokenSlice(value + 1), "empty")) return false,
            else => return false,
        }
    }
    var t = method.body_first + 1;
    if (t + 3 > method.body_last or tags[t] != .keyword_return or tags[t + 1] != .period or tags[t + 2] != .l_brace) return false;
    t += 3;
    while (t < method.body_last and tags[t] != .r_brace) {
        if (t + 3 > method.body_last or tags[t] != .period or tags[t + 1] != .identifier or tags[t + 2] != .equal) return false;
        t += 3;
        if (tags[t] != .identifier) return false;
        if (std.mem.eql(u8, tree.tokenSlice(t), param_name)) {
            t += 1;
        } else {
            const type_first = t;
            while (t + 2 <= method.body_last and tags[t + 1] == .period and tags[t + 2] == .identifier) t += 2;
            if (t == type_first or t + 3 > method.body_last or tags[t + 1] != .l_paren or
                tags[t + 2] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t + 2), param_name) or tags[t + 3] != .r_paren) return false;
            const nested = bindTypeRange(cache, tree, type_first, t - 2) orelse return false;
            if (!try allocatorFactory(cache, nested, tree.tokenSlice(t), depth + 1)) return false;
            t += 4;
        }
        if (tags[t] == .comma) t += 1 else if (tags[t] != .r_brace) return false;
    }
    return t + 2 == method.body_last and tags[t] == .r_brace and tags[t + 1] == .semicolon;
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

        // A method named like the destination field is still a call, not
        // a read of that field. Its returned storage has its own effects.
        if (t + 6 <= rbrace and
            (tags[t + 6] == .period or tags[t + 6] == .l_paren)) continue;

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
            dest = try bindDestination(state.cache, tree, init);
            dest_bound = true;
        }

        // The DESTINATION DECLARATION answers this copy, and nothing
        // else does.  What it runs on the field is the only question:
        // neither the spelling of the name nor a lifecycle call some
        // other type in the file happens to make on the same name has
        // any say in it.
        const verdict = try verdictOnField(state.cache, dest, dest_field);
        var balances_by_acquire = false;
        switch (verdict) {
            .borrowed => continue,
            .owned => |payload| balances_by_acquire = payload == .protocol,
            .unknown => continue,
        }

        // The same explicit-overlap proof applies to slices, pointers and
        // aggregate handles. Calling a field's deinit is not evidence that a
        // local source also has an implicit destructor.
        switch (try sliceLiteralIsHandoff(
            state.cache,
            tree,
            fn_decl,
            body,
            init,
            dest,
            field_tok,
            t + 3,
            source_field,
        )) {
            .handoff, .unknown => continue,
            .not_slice, .overlap => {},
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
            try copyIsAcquired(state.cache, tree, tags, fn_decl, body, field_tok, source_recv, source_field, dest.?)) continue;

        try report(gpa, state.problems, tree, field_tok, dest_field, source_recv);
    }
}

const SliceOwnership = enum { not_slice, handoff, overlap, unknown };

/// Raw slices require positive overlap evidence. Unknown effects cannot
/// prove either a single handoff or duplicate ownership.
fn sliceLiteralIsHandoff(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    fn_decl: Ast.Node.Index,
    body: Ast.Node.Index,
    init: Ast.Node.Index,
    dest: ?DestType,
    copy_token: Ast.TokenIndex,
    source_token: Ast.TokenIndex,
    field_name: []const u8,
) !SliceOwnership {
    const rhs_end = source_token + 3;
    if (rhs_end >= tree.tokens.len or
        (tree.tokenTag(rhs_end) != .comma and tree.tokenTag(rhs_end) != .r_brace)) return .not_slice;
    const resolver = cache.zls orelse return .not_slice;
    const rhs = cache.nodeForExactSpan(source_token, source_token + 2) orelse return .not_slice;
    const actual_type = (try resolver.resolutionFrame().typeOfNode(rhs)) orelse return .not_slice;
    const frame = resolver.resolutionFrame();
    if (try @import("../../cache/fresh_storage.zig").actualTypeAddressFree(frame, actual_type, 0, null))
        return .handoff;
    const destination = dest orelse return .unknown;
    _ = destination.info.findField(field_name) orelse return .unknown;

    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return .unknown;
    // The item arena outlives queries that grow the cache's binding table.
    const bindings = (try cache.localBindings(proto, body)).*;
    const local_dest = sliceLiteralBinding(tree, &bindings, init);
    var destination_uses: ?bool = null;
    if (local_dest) |local| {
        destination_uses = try sliceBindingUsesAreDisjoint(cache, tree, &bindings, body, local, field_name, null, false, false, null);
        if (destination_uses == true) return .handoff;
        // A local header has no implicit destructor. The source's cleanup or
        // publication is not a second obligation until this copy proves one.
        if (destination_uses == null) return .unknown;
    }

    const source = (bindings.findAt(tree.tokenSlice(source_token), source_token) orelse return .unknown).*;
    var source_error_cleanups: usize = 0;
    const source_uses = try sliceBindingUsesAreDisjoint(cache, tree, &bindings, body, source, field_name, source_token, false, true, &source_error_cleanups);
    if (source_uses == false) return .overlap;
    const fresh = switch (source.origin) {
        .call, .method_call, .try_call, .try_method_call => try cache.provesFreshStorage(
            @import("../../model/fn_summary.zig").claimFor(tree, &source),
            null,
        ),
        else => false,
    };
    const taken = if (fresh) true else try sliceOwnerWasTaken(cache, tree, &bindings, body, source, field_name, copy_token);
    if (taken == false and
        (local_dest == null or destination_uses == false)) return .overlap;
    if (local_dest) |local| {
        // A result's error cleanup is a duplicate only if the source also
        // retains an error cleanup. Otherwise it is the one local owner.
        const result_uses = try sliceBindingUsesAreDisjoint(cache, tree, &bindings, body, local, field_name, null, true, source_error_cleanups == 0, null);
        if (result_uses == false) return .overlap;
        if (result_uses == null or source_uses == null or taken == null) return .unknown;
        return .handoff;
    }
    if (source_uses == null or taken == null) return .unknown;
    const first = tree.firstToken(init);
    return if (first > 0 and tree.tokenTag(first - 1) == .keyword_return) .handoff else .unknown;
}

fn sliceLiteralBinding(
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    init: Ast.Node.Index,
) ?local_bindings.Binding {
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        const declaration = tree.fullVarDecl(node) orelse continue;
        if (declaration.ast.init_node.unwrap() != init) continue;
        const name_token = tree.nodeMainToken(node) + 1;
        return (bindings.findAt(tree.tokenSlice(name_token), name_token) orelse return null).*;
    }
    return null;
}

/// A take is authenticated by its exact local binding and owning slot.
/// No other alias, restore, or conditional clear may retain that slot.
fn sliceOwnerWasTaken(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    source: local_bindings.Binding,
    field_name: []const u8,
    copy: Ast.TokenIndex,
) !?bool {
    const tags = tree.tokens.items(.tag);
    const first = source.rhs_first;
    if (source.origin == .param) {
        var head = if (tags[first] == .asterisk) first + 1 else first;
        while (head <= source.rhs_last and tags[head] == .keyword_const) head += 1;
        const owner = bindTypeRange(cache, tree, head, source.rhs_last) orelse return null;
        // No automatic destruction is implied, but a pointer parameter's
        // declared owner remains in the caller unless this body disarms it.
        if (tags[first] != .asterisk) return null;
        // A borrowed pointer parameter also cannot donate its caller's
        // reference to a newly owning destination. It remains caller-visible.
        if ((try verdictOnField(cache, owner, field_name)) != .unknown) return false;
        return null;
    }
    if (!source.is_const) return null;
    if (source.rhs_last != first + 4 or tags[first] != .identifier or
        tags[first + 1] != .period or tags[first + 2] != .identifier or
        tags[first + 3] != .period or tags[first + 4] != .question_mark) return null;
    const owner_name = tree.tokenSlice(first);
    const owner = bindings.findAt(owner_name, first) orelse return null;
    if (owner.origin != .param or tags[owner.rhs_first] != .asterisk) return null;
    const owner_type = bindTypeRange(cache, tree, owner.rhs_first + 1, owner.rhs_last) orelse return null;
    if (try verdictOnField(cache, owner_type, tree.tokenSlice(first + 2)) != .owned) return null;
    const slot = tree.tokenSlice(first + 2);
    // An alias alone is unknown. A snapshot through that alias with its
    // own proved cleanup is a concrete second teardown obligation.
    for (bindings.items) |alias| {
        if (alias.origin != .alias or !std.mem.eql(u8, alias.origin.alias, owner_name)) continue;
        const root = bindings.findAt(owner_name, alias.rhs_first) orelse continue;
        if (root.name_token != owner.name_token) continue;
        for (bindings.items) |snapshot| {
            const at = snapshot.rhs_first;
            if (snapshot.rhs_last != at + 4 or tags[at] != .identifier or
                tags[at + 1] != .period or tags[at + 2] != .identifier or
                tags[at + 3] != .period or tags[at + 4] != .question_mark or
                !std.mem.eql(u8, tree.tokenSlice(at), alias.name) or
                !std.mem.eql(u8, tree.tokenSlice(at + 2), slot)) continue;
            const used_alias = bindings.findAt(alias.name, at) orelse continue;
            if (used_alias.name_token != alias.name_token) continue;
            if (try sliceBindingUsesAreDisjoint(cache, tree, bindings, body, snapshot, field_name, null, false, false, null) == false)
                return false;
        }
    }
    const body_first = tree.firstToken(body);
    const body_last = tree.lastToken(body);
    var frames: ReachFrames = .{};
    collectReachFrames(tags, body_first, body_last, &frames);
    var cleared = false;
    var unknown = false;
    var t = body_first;
    while (t + 2 <= body_last) : (t += 1) {
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), owner_name)) continue;
        if (t > body_first and tags[t - 1] == .period) continue;
        const used_owner = bindings.findAt(owner_name, t) orelse {
            unknown = true;
            continue;
        };
        if (used_owner.name_token != owner.name_token) continue;
        // A pointer alias, address escape, or receiver call could take a
        // second snapshot through another spelling. Only direct members
        // are admitted; the selected slot is checked separately below.
        if (tags[t + 1] != .period or tags[t + 2] != .identifier or
            (t + 3 <= body_last and tags[t + 3] == .l_paren)) {
            unknown = true;
            continue;
        }
        if (!isRecvFieldAt(tree, tags, t, body_last, owner_name, slot)) continue;
        if (t == first) continue;
        if (t + 5 > body_last or tags[t + 3] != .equal or
            tags[t + 4] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t + 4), "null") or
            tags[t + 5] != .semicolon) {
            unknown = true;
            continue;
        }
        if (t <= source.rhs_last or t >= copy or cleared) {
            unknown = true;
            continue;
        }
        if (sliceDeferredAt(tree, t) == .error_only) return false;
        if (!reachesCopy(&frames, t, copy)) return false;
        cleared = true;
        t += 5;
    }
    return if (unknown) null else cleared;
}

const SliceDeferred = enum { immediate, error_only, unconditional };

fn sliceDeferredAt(tree: *const Ast, use: Ast.TokenIndex) SliceDeferred {
    var result: SliceDeferred = .immediate;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"defer" and tag != .@"errdefer") continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) > use or tree.lastToken(node) < use) continue;
        if (tag == .@"defer") return .unconditional;
        result = .error_only;
    }
    return result;
}

/// Select the innermost real call containing a use, not a method-name
/// heuristic. Its complete outcome summary is the non-cleanup certificate.
fn sliceCallContaining(tree: *const Ast, use: Ast.TokenIndex) ?Ast.Node.Index {
    var found: ?Ast.Node.Index = null;
    var width: Ast.TokenIndex = std.math.maxInt(Ast.TokenIndex);
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        _ = tree.fullCall(&buffer, node) orelse continue;
        const first = tree.firstToken(node);
        const last = tree.lastToken(node);
        if (first <= use and use <= last and last - first < width) {
            found = node;
            width = last - first;
        }
    }
    return found;
}

fn sliceBindingUsesAreDisjoint(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    local: local_bindings.Binding,
    field: ?[]const u8,
    copy_use: ?Ast.TokenIndex,
    allow_return: bool,
    allow_error_cleanup: bool,
    cleanup_count: ?*usize,
) anyerror!?bool {
    const tags = tree.tokens.items(.tag);
    const last = @min(local.scope_close, tree.lastToken(body));
    var last_error_cleanup: ?Ast.TokenIndex = null;
    var returns: usize = 0;
    var unknown = false;
    var t = local.name_token + 1;
    while (t <= last) : (t += 1) {
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), local.name)) continue;
        if (t > 0 and tags[t - 1] == .period) continue;
        const used = bindings.findAt(local.name, t) orelse {
            unknown = true;
            continue;
        };
        if (used.name_token != local.name_token) continue;
        if (copy_use == t) {
            t += 2;
            continue;
        }
        // Reading/writing another scalar member does not alias this slice.
        if (field) |selected| {
            if (t + 2 <= last and tags[t + 1] == .period and tags[t + 2] == .identifier and
                !std.mem.eql(u8, tree.tokenSlice(t + 2), selected) and
                (t + 3 > last or tags[t + 3] != .l_paren) and
                try sliceMemberIsScalar(cache, t, t + 2)) continue;
        }
        // Follow local headers/slices/addresses that could carry this
        // storage. Descents strictly advance declaration tokens: no cap
        // or guessed alias names are needed, and no cycle can recurse.
        var derived: ?local_bindings.Binding = null;
        for (bindings.items) |candidate| {
            if (candidate.name_token <= local.name_token or candidate.origin == .param or
                candidate.origin == .loop_capture or t < candidate.rhs_first or t > candidate.rhs_last) continue;
            if (derived == null or candidate.rhs_last - candidate.rhs_first <
                derived.?.rhs_last - derived.?.rhs_first) derived = candidate;
        }
        if (derived) |alias| {
            if (try sliceMemberIsScalar(cache, alias.rhs_first, alias.rhs_last)) {
                t = alias.rhs_last;
                continue;
            }
            // Unread call results and opaque aliases are not overlap proof.
            switch (alias.origin) {
                .call, .method_call, .try_call, .try_method_call, .unknown => unknown = true,
                else => {
                    const alias_uses = try sliceBindingUsesAreDisjoint(cache, tree, bindings, body, alias, null, null, false, false, null);
                    if (alias_uses == false) return false;
                    if (alias_uses == null) unknown = true;
                },
            }
            t = alias.rhs_last;
            continue;
        }
        if (sliceCallContaining(tree, t)) |call_node| {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, call_node).?;
            const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)) orelse {
                unknown = true;
                t = tree.lastToken(call_node);
                continue;
            };
            const summary = try cache.summaryOfResolvedMethod(actual.callee);
            // Standard allocator release primitives have declared SDK
            // semantics even when their implementation's generic helpers
            // cannot produce a complete ordered function summary.
            const releases = if (try sliceAllocatorReleasesLocal(cache, tree, bindings, actual, local, field) or
                try sliceDeclaredCleanup(cache, tree, bindings, actual, local, field))
                1
            else if (summary) |known|
                if (known.normal_success_storage_effects_complete)
                    try sliceCallReleaseCount(cache, tree, bindings, actual, known.normal_success_storage_outcomes, local, field)
                else
                    0
            else
                0;
            if (releases != 0) {
                const deferred = sliceDeferredAt(tree, t);
                if (deferred != .error_only) return false;
                // An errdefer without a later error exit cannot run.
                if (!sliceHasLaterErrorExit(tree, body, t)) {
                    t = tree.lastToken(call_node);
                    continue;
                }
                if (releases > 1 or !allow_error_cleanup) return false;
                if (last_error_cleanup) |previous| {
                    if (sliceCleanupScopeContains(tree, body, previous, t) and
                        sliceCleanupScopeContains(tree, body, t, previous)) return false;
                }
                last_error_cleanup = t;
                if (cleanup_count) |count| {
                    if (copy_use == null or sliceCleanupScopeContains(tree, body, t, copy_use.?)) count.* += 1;
                }
            } else {
                const known = summary orelse {
                    unknown = true;
                    t = tree.lastToken(call_node);
                    continue;
                };
                if (!known.normal_success_effects_complete or
                    !known.error_effects_complete or
                    !try sliceCallCannotPublish(cache, actual)) unknown = true;
                if (known.normal_success_effects_complete and
                    try sliceCallPublishesLocal(cache, tree, bindings, actual, local, field)) return false;
                for (known.retained_owned_params) |parameter| {
                    if (try sliceCallNamesLocal(cache, tree, bindings, actual, .{ .param = parameter, .path = "" }, local, null))
                        return false;
                }
            }
            t = tree.lastToken(call_node);
            continue;
        }
        if (t > 0 and tags[t - 1] == .keyword_return and t + 1 <= last and tags[t + 1] == .semicolon) {
            if (!allow_return) {
                if (try sliceReturnOwnsPayload(cache, tree, t, field)) return false;
                unknown = true;
                continue;
            }
            if (returns != 0) unknown = true;
            returns += 1;
            continue;
        }
        // Plain element access and slice length inspect the allocation;
        // they do not hand an owning header to another cleanup.
        var after = t + 1;
        if (field != null and after + 1 <= last and tags[after] == .period and tags[after + 1] == .identifier)
            after += 2;
        if (after <= last and tags[after] == .l_bracket) {
            if (t > 0 and (tags[t - 1] == .ampersand or tags[t - 1] == .keyword_return)) {
                unknown = true;
                continue;
            }
            const close = tokens.matchBracket(tags, after, last) orelse {
                unknown = true;
                continue;
            };
            var k = after + 1;
            while (k < close) : (k += 1) {
                if (tags[k] == .ellipsis2) unknown = true;
            }
            continue;
        }
        if (after + 1 <= last and tags[after] == .period and tags[after + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(after + 1), "len")) continue;
        // Error-only resets do not disarm the caller's owner on success.
        if (field != null and t + 8 <= last and tags[t + 1] == .period and
            tags[t + 2] == .identifier and std.mem.eql(u8, tree.tokenSlice(t + 2), field.?) and
            tags[t + 3] == .equal and tags[t + 4] == .ampersand and
            tags[t + 5] == .period and tags[t + 6] == .l_brace and
            tags[t + 7] == .r_brace and tags[t + 8] == .semicolon and
            sliceDeferredAt(tree, t) == .error_only) {
            t += 8;
            continue;
        }
        if (copy_use) |copy| {
            if (t > copy and t + 8 <= last and tags[t + 1] == .period and
                tags[t + 2] == .identifier and tags[t + 3] == .equal and
                tags[t + 4] == .ampersand and tags[t + 5] == .period and
                tags[t + 6] == .l_brace and tags[t + 7] == .r_brace and
                tags[t + 8] == .semicolon and
                sliceClearHasSuccessfulBypass(tree, bindings, body, copy, t)) return false;
        }
        if (try sliceUseIsOwningStore(cache, tree, bindings, t)) return false;
        if (try sliceUseIsOwningLiteral(cache, tree, t)) return false;
        unknown = true;
    }
    if (unknown or (allow_return and returns != 1)) return null;
    return true;
}

fn sliceMemberIsScalar(cache: *file_cache_mod.FileCache, first: Ast.TokenIndex, last: Ast.TokenIndex) !bool {
    const resolver = cache.zls orelse return false;
    const node = cache.nodeForExactSpan(first, last) orelse return false;
    const frame = resolver.resolutionFrame();
    const actual = (try frame.typeOfNode(node)) orelse return false;
    return @import("../../cache/fresh_storage.zig").actualTypeAddressFree(frame, actual, 0, null);
}

fn sliceCleanupScopeClose(tree: *const Ast, body: Ast.Node.Index, use: Ast.TokenIndex) Ast.TokenIndex {
    var registration = use;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"errdefer") continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) <= use and tree.lastToken(node) >= use)
            registration = @min(registration, tree.firstToken(node));
    }
    var close = tree.lastToken(body);
    var at = tree.firstToken(body);
    while (at < registration) : (at += 1) {
        if (tree.tokenTag(at) != .l_brace) continue;
        const end = matchingBrace(tree, at);
        if (end > use) close = @min(close, end);
    }
    return close;
}

fn sliceCleanupScopeContains(tree: *const Ast, body: Ast.Node.Index, cleanup: Ast.TokenIndex, use: Ast.TokenIndex) bool {
    const close = sliceCleanupScopeClose(tree, body, cleanup);
    if (use > close) return false;
    var first = tree.firstToken(body);
    var at = first;
    while (at < cleanup) : (at += 1) {
        if (tree.tokenTag(at) == .l_brace and matchingBrace(tree, at) == close) first = at;
    }
    return first <= use;
}

fn sliceHasLaterErrorExit(tree: *const Ast, body: Ast.Node.Index, cleanup: Ast.TokenIndex) bool {
    const close = sliceCleanupScopeClose(tree, body, cleanup);
    var first = cleanup;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"errdefer") continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) <= cleanup and tree.lastToken(node) >= cleanup)
            first = @max(first, tree.lastToken(node));
    }
    var at = first + 1;
    while (at < close) : (at += 1) {
        if (tree.tokenTag(at) == .keyword_try) return true;
        if (tree.tokenTag(at) == .keyword_return and at + 1 < close and
            tree.tokenTag(at + 1) == .keyword_error) return true;
    }
    return false;
}

fn sliceReturnOwnsPayload(cache: *file_cache_mod.FileCache, tree: *const Ast, use: Ast.TokenIndex, field: ?[]const u8) !bool {
    const fn_decl = tokens.enclosingFnDecl(tree, use) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, fn_decl) orelse return false;
    var result = proto.ast.return_type.unwrap() orelse return false;
    while (tree.nodeTag(result) == .error_union)
        result = tree.nodeData(result).node_and_node[1];
    const owner = bindTypeExpr(cache, tree, result) orelse return false;
    if (field) |selected| return (try verdictOnField(cache, owner, selected)) == .owned;
    for (owner.info.fields) |member| {
        if ((try verdictOnField(cache, owner, member.name)) == .owned) return true;
    }
    return false;
}

fn sliceAllocatorReleasesLocal(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    actual: file_cache_mod.FileCache.ActualCallSummary,
    local: local_bindings.Binding,
    field: ?[]const u8,
) !bool {
    const primitive = (try @import("../../cache/fresh_storage.zig").allocatorPrimitive(cache, actual, .{
        .claim = .{ .first = tree.firstToken(actual.callee.call_node), .last = tree.lastToken(actual.callee.call_node) },
        .depth = 0,
        .frame = actual.callee.caller_frame,
    })) orelse return false;
    if (primitive.operation != .release) return false;
    const parameter = primitive.previous_parameter orelse return false;
    const resolver = cache.zls orelse return false;
    const frame = actual.callee.caller_frame orelse resolver.resolutionFrame();
    var buffer: [2]Ast.Node.Index = undefined;
    const allocator = (try actual.callArgumentFor(cache, &buffer, primitive.allocator_parameter)) orelse return false;
    if ((try frame.isStdAllocator(allocator)) != true) return false;
    return sliceCallNamesLocal(cache, tree, bindings, actual, .{ .param = parameter, .path = "" }, local, field);
}

/// Count releases of the selected entry payload in complete, correlated
/// outcomes. A failure to prove independent payloads is not a double free.
fn sliceCallReleaseCount(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    actual: file_cache_mod.FileCache.ActualCallSummary,
    outcomes: []const @import("../../model/fn_summary.zig").StorageOutcome,
    local: local_bindings.Binding,
    field: ?[]const u8,
) !usize {
    var most: usize = 0;
    for (outcomes) |outcome| {
        var releases: usize = 0;
        var replaced = false;
        for (outcome.operations) |operation| {
            if (!try sliceCallNamesLocal(cache, tree, bindings, actual, operation.path, local, field)) continue;
            if (operation.kind == .replace) {
                replaced = true;
                continue;
            }
            if (operation.version) |version| {
                if (version != 0) continue;
            } else if (replaced) continue;
            releases += 1;
        }
        most = @max(most, releases);
    }
    return most;
}

/// Match a formal release to the exact current local binding and field.
/// Unknown aliases and different fields supply no release evidence.
fn sliceCallNamesLocal(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    actual: file_cache_mod.FileCache.ActualCallSummary,
    path: @import("../../model/fn_summary.zig").ParamPath,
    local: local_bindings.Binding,
    field: ?[]const u8,
) !bool {
    var buffer: [2]Ast.Node.Index = undefined;
    const argument = (try actual.callArgumentFor(cache, &buffer, path.param)) orelse return false;
    var evidence: reference_ownership.Query = .{};
    if (field) |selected| {
        if (std.mem.eql(u8, path.path, selected))
            return evidence.namesResource(cache, bindings, argument, local.name_token, "");
        if (path.path.len == 0)
            return evidence.namesResource(cache, bindings, argument, local.name_token, selected);
        return false;
    }
    _ = tree;
    return evidence.namesResource(cache, bindings, argument, local.name_token, "");
}

/// A source-visible lifecycle invocation is a MAY cleanup obligation even
/// when its heap summary contains no deallocation (for example a refcount
/// decrement). It can establish overlap, never balance or disarm a copy.
fn sliceDeclaredCleanup(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    actual: file_cache_mod.FileCache.ActualCallSummary,
    local: local_bindings.Binding,
    field: ?[]const u8,
) !bool {
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    const model = try declaring.fileModel();
    if (model.tree != actual.callee.tree) return false;
    for (model.types) |*owner| {
        for (owner.methods) |*method| {
            if (method.fn_decl != actual.callee.declaration) continue;
            const receiver = method.receiver orelse return false;
            if (field) |selected| {
                if (isRefReleaseName(method.name) and
                    try sliceCallNamesLocal(cache, tree, bindings, actual, .{ .param = 0, .path = "" }, local, selected)) return true;
                if ((try methodReachesField(cache, model.tree, owner, method, receiver.name, selected)) == null) return false;
                return sliceCallNamesLocal(cache, tree, bindings, actual, .{ .param = 0, .path = selected }, local, selected);
            }
            for (owner.fields) |member| {
                if ((try methodReachesField(cache, model.tree, owner, method, receiver.name, member.name)) == null) continue;
                if (try sliceCallNamesLocal(cache, tree, bindings, actual, .{ .param = 0, .path = member.name }, local, null)) return true;
            }
            return false;
        }
    }
    return false;
}

/// A second returned owning literal is a positive owning use, not an
/// opaque escape. A discarded or unread temporary literal proves nothing.
fn sliceUseIsOwningLiteral(cache: *file_cache_mod.FileCache, tree: *const Ast, use: Ast.TokenIndex) !bool {
    if (use < 3 or tree.tokenTag(use - 1) != .equal or
        tree.tokenTag(use - 2) != .identifier or tree.tokenTag(use - 3) != .period) return false;
    var owner = false;
    var returned = false;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, node) orelse continue;
        if (tree.firstToken(node) > use or tree.lastToken(node) < use) continue;
        const first = tree.firstToken(node);
        if (first > 0 and tree.tokenTag(first - 1) == .keyword_return) returned = true;
        for (literal.ast.fields) |value| {
            if (tree.firstToken(value) != use) continue;
            const dest = try bindDestination(cache, tree, node);
            owner = try verdictOnField(cache, dest, tree.tokenSlice(use - 2)) == .owned;
        }
    }
    return owner and returned;
}

fn sliceUseIsOwningStore(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    use: Ast.TokenIndex,
) !bool {
    if (use < 4 or tree.tokenTag(use - 1) != .equal or
        tree.tokenTag(use - 2) != .identifier or tree.tokenTag(use - 3) != .period or
        tree.tokenTag(use - 4) != .identifier) return false;
    const receiver = bindings.findAt(tree.tokenSlice(use - 4), use - 4) orelse return false;
    if (receiver.origin != .param or tree.tokenTag(receiver.rhs_first) != .asterisk) return false;
    const owner = bindTypeRange(cache, tree, receiver.rhs_first + 1, receiver.rhs_last) orelse return false;
    return (try verdictOnField(cache, owner, tree.tokenSlice(use - 2))) == .owned;
}

/// A runtime branch that jumps past a clear and reaches a successful
/// return leaves the caller's original owner live beside the saved copy.
/// Do not infer this from an unread helper or a failed disarm proof.
fn sliceClearHasSuccessfulBypass(
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    copy: Ast.TokenIndex,
    clear: Ast.TokenIndex,
) bool {
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        const branch = tree.fullIf(node) orelse continue;
        if (tree.firstToken(node) <= copy or tree.lastToken(node) >= clear or
            tree.nodeTag(branch.ast.cond_expr) != .identifier) continue;
        const condition_token = tree.nodeMainToken(branch.ast.cond_expr);
        const condition = bindings.findAt(tree.tokenSlice(condition_token), condition_token) orelse continue;
        var runtime_condition = condition.origin == .param;
        if (condition.origin == .loop_capture) {
            var at = condition.rhs_first;
            while (at <= condition.rhs_last) : (at += 1) {
                if (tree.tokenTag(at) != .identifier) continue;
                const value = bindings.findAt(tree.tokenSlice(at), at) orelse continue;
                if (value.origin == .param) runtime_condition = true;
            }
        }
        if (!runtime_condition) continue;
        const jump = branch.ast.then_expr;
        const jump_tag = tree.nodeTag(jump);
        if (jump_tag != .@"break" and jump_tag != .@"continue") continue;
        const jump_token = tree.nodeMainToken(jump);
        for (tree.nodes.items(.tag), 0..) |_, target_index| {
            const target: Ast.Node.Index = @enumFromInt(target_index);
            const first = tree.firstToken(target);
            const last = tree.lastToken(target);
            if (first >= copy or last <= clear or last >= tree.lastToken(body)) continue;
            if (jump_tag == .@"break") {
                if (jump_token + 2 >= tree.tokens.len or tree.tokenTag(jump_token + 1) != .colon or
                    tree.tokenTag(first) != .identifier or tree.tokenTag(first + 1) != .colon or
                    !std.mem.eql(u8, tree.tokenSlice(first), tree.tokenSlice(jump_token + 2))) continue;
            } else {
                // A single fixed iteration reaches the return after a
                // continue; an unbounded loop supplies no success proof.
                const loop = tree.fullFor(target) orelse continue;
                if (loop.ast.inputs.len != 1) continue;
                var array_buffer: [2]Ast.Node.Index = undefined;
                const input = tree.fullArrayInit(&array_buffer, loop.ast.inputs[0]) orelse continue;
                if (input.ast.elements.len != 1) continue;
            }
            var at = last + 1;
            // Only a direct successful return after the target is a proof.
            if (tree.tokenTag(at) == .semicolon) at += 1;
            if (tree.tokenTag(at) == .keyword_return) return true;
        }
    }
    return false;
}

/// A direct store into a declared global owner is positive publication
/// evidence. Unknown calls or an address encoded in a scalar are not.
fn sliceCallPublishesLocal(
    cache: *file_cache_mod.FileCache,
    caller_tree: *const Ast,
    caller_bindings: *const local_bindings.LocalBindings,
    actual: file_cache_mod.FileCache.ActualCallSummary,
    local: local_bindings.Binding,
    field: ?[]const u8,
) !bool {
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    const tree = actual.callee.tree;
    const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, actual.callee.declaration) orelse return false;
    const bindings = (try declaring.localBindings(proto, body)).*;
    var frames: ReachFrames = .{};
    collectReachFrames(tree.tokens.items(.tag), tree.firstToken(body), tree.lastToken(body), &frames);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .assign) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) < tree.firstToken(body) or tree.lastToken(node) > tree.lastToken(body)) continue;
        const pair = tree.nodeData(node).node_and_node;
        if (tree.nodeTag(pair[0]) != .field_access or tree.nodeTag(pair[1]) != .field_access) continue;
        const target = tree.nodeData(pair[0]).node_and_token;
        const source = tree.nodeData(pair[1]).node_and_token;
        if (tree.nodeTag(target[0]) != .identifier or tree.nodeTag(source[0]) != .identifier) continue;
        const target_token = tree.nodeMainToken(target[0]);
        const source_token = tree.nodeMainToken(source[0]);
        if (bindings.findAt(tree.tokenSlice(target_token), target_token) != null or
            !reachesCopy(&frames, source_token, tree.lastToken(body))) continue;
        const source_binding = bindings.findAt(tree.tokenSlice(source_token), source_token) orelse continue;
        if (source_binding.origin != .param) continue;
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            if (parameter.name_token != source_binding.name_token) continue;
            if (!try sliceCallNamesLocal(cache, caller_tree, caller_bindings, actual, .{
                .param = parameter_index,
                .path = tree.tokenSlice(source[1]),
            }, local, field)) break;
            for (tree.nodes.items(.tag), 0..) |_, declaration_index| {
                const declaration_node: Ast.Node.Index = @enumFromInt(declaration_index);
                const declaration = tree.fullVarDecl(declaration_node) orelse continue;
                const name_token = tree.nodeMainToken(declaration_node) + 1;
                if (!std.mem.eql(u8, tree.tokenSlice(name_token), tree.tokenSlice(target_token)) or
                    tokens.enclosingFnDecl(tree, name_token) != null) continue;
                const type_expr = declaration.ast.type_node.unwrap() orelse continue;
                const owner = bindTypeExpr(declaring, tree, type_expr) orelse continue;
                if ((try verdictOnField(declaring, owner, tree.tokenSlice(target[1]))) == .owned) return true;
            }
            break;
        }
    }
    return false;
}

/// Complete no-release outcomes do not say whether a callee publishes the
/// slice. Require a void success result and certified effects on every
/// formal and unrooted storage. A scalar result can encode an address.
/// The whole read-only query may stop at its first write, so its other
/// classifications are NOT complete certificates.
fn sliceCallCannotPublish(
    cache: *file_cache_mod.FileCache,
    actual: file_cache_mod.FileCache.ActualCallSummary,
) !bool {
    const resolver = cache.zls orelse return false;
    const frame = actual.callee.caller_frame orelse resolver.resolutionFrame();
    var result = (try frame.typeOfNode(actual.callee.call_node)) orelse return false;
    while (resolver.typeTag(result) == .error_union) {
        const child = resolver.childType(result) orelse return false;
        result = (try resolver.normalizedType(child)) orelse return false;
    }
    if (resolver.typeTag(result) != .void) return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = cache.tree.fullCall(&call_buffer, actual.callee.call_node) orelse return false;
    const token = cache.tree.nodeMainToken(call.ast.fn_expr);
    const context: @import("../../cache/call_summary.zig").QueryContext = .{
        .frame = actual.callee.caller_frame,
    };
    const whole = (try cache.callEffectAt(token, .{ .whole = actual.callee }, context)) orelse return false;
    if (whole == .read_only) return true;

    // A finish-style scalar writer has no nested calls that might retain
    // arguments or use collection append's weaker no-invalidation shortcut.
    // Reuse the existing intrinsic/AST classifier; opaque syntax fails shut.
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    const tree = actual.callee.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, actual.callee.declaration) orelse return false;
    const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return false;
    const bindings = (try declaring.localBindings(proto, body)).*;
    var scan = @import("../../cache/call_effects.zig").Scan.init(tree, actual.callee.declaration, &bindings);
    while (try scan.next()) |event| {
        switch (event) {
            .call, .write_or_unknown => return false,
            .node, .write => {},
        }
    }
    const global = (try cache.callEffectAt(token, .unrooted, context)) orelse return false;
    if (global != .read_only) return false;
    var parameters = proto.iterate(tree);
    var parameter: u32 = 0;
    while (parameters.next() != null) : (parameter += 1) {
        // The default complete query must scan past scalar stores. A
        // read-only-only/whole early negative answer could hide publication.
        const effect = (try cache.callEffectAt(token, .{ .parameter = .{
            .param = parameter,
        } }, context)) orelse return false;
        switch (effect) {
            .read_only, .writes_without_invalidation => {},
            .may_invalidate, .unknown => return false,
        }
    }
    return true;
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
    dest: DestType,
) !bool {
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return false;
    var evidence: reference_ownership.Query = .{};
    const teardown = (try lifecycleMethodOnField(cache, dest.tree, dest.info, source_field)) orelse return false;
    const protocol: reference_ownership.ReleaseProtocol = .{
        .tree = dest.tree,
        .declaration = dest.info.findMethod(teardown.method).?.fn_decl,
        .field = source_field,
    };
    return hasCanonicalAcquireCall(&evidence, cache, proto, body, tree, tags, tree.firstToken(body), field_tok, source_recv, source_field, protocol);
}

/// Only the shared declaration-bound increment query can balance a copy.
fn hasCanonicalAcquireCall(
    evidence: *reference_ownership.Query,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    copy: Ast.TokenIndex,
    source: []const u8,
    path: []const u8,
    protocol: reference_ownership.ReleaseProtocol,
) !bool {
    const bindings = (try cache.localBindings(proto, body)).*;
    const binding = (bindings.findAt(source, copy) orelse return false).*;
    var frames: ReachFrames = .{};
    collectReachFrames(tags, start, copy, &frames);
    const declaration = tokens.enclosingFnDecl(tree, copy) orelse return false;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        const at = tree.firstToken(node);
        if (at < start or tree.lastToken(node) >= copy) continue;
        if (tokens.enclosingFnDecl(tree, at) != declaration) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (deferredCall(tree, at) or !reachesCopy(&frames, at, copy)) continue;
        switch (try evidence.acquisitionForResourceAt(cache, fresh_storage.calleeQueryToken(tree, call), proto, body, binding.name_token, path, copy, protocol)) {
            .increment => return true,
            .unknown, .refused => {},
        }
    }
    return false;
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
) !?DestType {
    var buffer: [2]Ast.Node.Index = undefined;
    const literal = tree.fullStructInit(&buffer, init) orelse return null;
    if (literal.ast.type_expr.unwrap()) |type_expr| return bindTypeExpr(cache, tree, type_expr);
    return contextualDestination(cache, tree, init);
}

/// The declaration an ANONYMOUS literal (`.{ … }`) constructs, read
/// from what its own context says the value is: the type the enclosing
/// function returns, an annotated local, or a callee's argument type.
///
/// The context is the only thing that names it.  Reading the SOURCE's
/// type instead would answer the question the literal was written to
/// ask about the wrong declaration — and would declare a borrowed view
/// an owner whenever the two happened to differ, which is exactly the
/// case worth getting right. Nested literals use their own canonical
/// result-location type, never the outer literal's type.
fn contextualDestination(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    init: Ast.Node.Index,
) !?DestType {
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

    if (tags[before] == .comma or tags[before] == .l_paren)
        return argumentDestination(cache, tree, init);

    // `const name : Type = .{ … }` — the annotation names the type the
    // local is declared with, which is the type the literal constructs.
    if (tags[before] != .equal or before == 0) return null;
    const name_last = before - 1;
    if (tags[name_last] != .identifier) return null;
    const colon = annotationColonBefore(tags, name_last) orelse
        return expectedDestination(cache, tree, init);
    return bindTypeRange(cache, tree, colon + 1, name_last);
}

/// Only the literal occupying an actual argument can use that call's
/// parameter context. Nested fields and chained expressions cannot inherit
/// a type from an enclosing call. The canonical expected-type query handles
/// argument indexes, explicit/static calls, and implicit method receivers.
fn argumentDestination(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    init: Ast.Node.Index,
) !?DestType {
    const resolver = cache.zls orelse return null;
    if (tree != cache.tree or tree != &resolver.handle.document.tree) return null;
    const calls = try cache.getCallIndex();
    var iterator = calls.by_callee_token.valueIterator();
    var is_argument = false;
    while (iterator.next()) |call_node| {
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, call_node.*) orelse continue;
        if (std.mem.findScalar(Ast.Node.Index, call.ast.params, init) != null) {
            is_argument = true;
            break;
        }
    }
    if (!is_argument) return null;
    return expectedDestination(cache, tree, init);
}

/// Preserve the exact declaring document of a contextual aggregate type.
fn expectedDestination(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    init: Ast.Node.Index,
) !?DestType {
    const resolver = cache.zls orelse return null;
    if (tree != cache.tree or tree != &resolver.handle.document.tree) return null;
    var expected = (try resolver.resolutionFrame().expectedTypeOfNode(init)) orelse return null;
    while (resolver.typeTag(expected) == .optional)
        expected = resolver.childType(expected) orelse return null;
    const container = switch (expected.data) {
        .container => |container| container,
        else => return null,
    };
    // The rule's declaration model is syntactic, not an instantiated
    // teardown model. Do not discard generic bindings when judging ownership.
    if (container.bound_params.count() != 0 or container.bound_values.count() != 0) return null;
    const declaring_tree = &container.scope_handle.handle.document.tree;
    const declaration = container.scope_handle.toNode();
    if (declaration == .root) return null;
    const main_token = declaring_tree.nodeMainToken(declaration);
    if (declaring_tree.tokenTag(main_token) != .keyword_struct) return null;
    const first = main_token + 1;
    if (declaring_tree.tokenTag(first) != .l_brace) return null;
    const model = if (declaring_tree == tree)
        try cache.fileModel()
    else model: {
        const project = cache.project orelse return null;
        var scratch = std.heap.stackFallback(std.Io.Dir.max_path_bytes, cache.gpa);
        const allocator = scratch.get();
        const path = try container.scope_handle.handle.document.uri.toFsPath(allocator);
        defer allocator.free(path);
        break :model (try project.modelForPath(path)) orelse return null;
    };
    // Model and resolver must name the same immutable document, never an
    // unrelated same-named type or a reloaded source snapshot.
    if (model.tree != declaring_tree) return null;
    const last = declaring_tree.lastToken(declaration);
    for (model.types) |*info| {
        if (info.kind == .struct_ and info.body_first == first and
            info.body_last == last)
            return .{ .tree = model.tree, .info = info };
    }
    return null;
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
    // An import alias identifies another source. Resolve the whole path
    // there before consulting local declarations, so a same-named local
    // type cannot replace the imported owner.
    if (len > 1 and headIsImportAlias(tree, path[0])) {
        if (cache.importedTypeAcrossImports(path[0..len])) |resolved| {
            return .{ .tree = resolved.model.tree, .info = resolved.info };
        }
        return null;
    }
    if (model.findQualifiedType(path[0..len])) |info| {
        return .{ .tree = model.tree, .info = info };
    }
    // An exact bound import path or bare type alias retains its declaring
    // source, without searching unrelated leaves or the project-wide index.
    if (cache.importedTypeAcrossImports(path[0..len])) |resolved| {
        return .{ .tree = resolved.model.tree, .info = resolved.info };
    }
    return null;
}

/// True iff `name` is bound to an `@import` at the top level of this
/// file: `const imported = @import("shapes.zig");`.
/// `tree` is the root document admitted by `check`; this helper is only
/// called after bindTypeRange verifies model.tree == tree.
fn headIsImportAlias(tree: *const Ast, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    const last = tags.len;
    var t: Ast.TokenIndex = 0;
    while (last - t > 5) : (t += 1) {
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
) !FieldVerdict {
    const d = dest orelse return .unknown;
    const field = d.info.findField(field_name) orelse return .unknown;
    // A standard allocator descriptor copied by value is a capability,
    // even when this declaration uses it to tear down other fields.
    // A pointer to that descriptor still carries an ownership obligation.
    if (try isBorrowedAllocatorValue(cache, d.tree, d.info, field_name)) return .borrowed;
    if (try lifecycleMethodOnField(cache, d.tree, d.info, field_name)) |teardown| {
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
) !?Teardown {
    // Imported declaration trees have their own source/index domain.
    if (tree != cache.tree) _ = try admitSource(tree);
    for (ti.methods) |*m| {
        const receiver = m.receiver orelse continue;
        const payload = (try methodReachesField(cache, tree, ti, m, receiver.name, field_name)) orelse continue;
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
) !?Payload {
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
        const payload = try handoffPayload(cache, tree, ti, m, h, call, close, recv, field_name);
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
) !Payload {
    const tags = tree.tokens.items(.tag);
    const handoff = tree.tokenSlice(call);
    const declared = headTypeRange(tree, ti, m, head, recv) orelse return .unknown;
    // A genuine allocator head is the release mechanism, not the payload.
    // Auto-deref through a pointer still frees the argument, never the
    // descriptor. Passing that descriptor as an argument is a separate
    // ownership question and must not receive the by-value exemption.
    if (try isAllocatorType(cache, tree, declared, true)) return .destroyed_argument;
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
    if (passed_at != null and try isBorrowedAllocatorValue(cache, tree, ti, field_name))
        return .borrowed_argument;
    const owner = declaredTypeDeclAt(cache, tree, declared.first, declared.last) orelse return .unknown;
    if (owner.tree != tree) _ = try admitSource(owner.tree);
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
) !bool {
    const field = ti.findField(field_name) orelse return false;
    return isAllocatorType(cache, tree, .{ .first = field.type_first, .last = field.type_last }, false);
}

/// Authenticate SDK identity in the exact declaration's resolution frame.
/// Unresolved actual identity stays unknown; actual query errors propagate.
/// Token-only runs retain the existing lexical import proof.
fn isAllocatorType(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    declared: TypeRange,
    allow_pointer: bool,
) !bool {
    if (tree != cache.tree) {
        // Foreign token positions belong to the declaration's document.
        // Use its own lexical scope proof, not the caller's SDK frame or
        // bindings. A shadowed or unresolved std alias remains unknown.
        var declaring = file_cache_mod.FileCache.init(cache.gpa, tree);
        defer declaring.deinit();
        return std_type_query.isType(&declaring, tree, declared.first, declared.last, "mem", "Allocator", .{
            .allow_pointer = allow_pointer,
        });
    }
    if (cache.zls) |resolver| {
        const node = cache.nodeForExactSpan(declared.first, declared.last) orelse return false;
        const frame = resolver.resolutionFrame();
        if (!allow_pointer) {
            const actual = (try frame.typeOfNode(node)) orelse return false;
            // Optional/pointer descriptors are owned storage, not capability
            // values. containerOfNode auto-derefs, so check the wrapper first.
            if (resolver.typeTag(actual) != .@"struct") return false;
        }
        return (try frame.isStdAllocator(node)) == true;
    }
    return std_type_query.isType(cache, tree, declared.first, declared.last, "mem", "Allocator", .{
        .allow_pointer = allow_pointer,
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
    if (first > last) return null;
    const tags = tree.tokens.items(.tag);
    var head = first;
    while (head <= last) : (head += 1) {
        switch (tags[head]) {
            .question_mark, .asterisk, .asterisk_asterisk, .keyword_const, .keyword_volatile, .keyword_allowzero => {},
            .identifier => break,
            else => return null,
        }
    }
    if (head > last) return null;
    if (head < last) return bindTypeRange(cache, tree, head, last);
    const name = tree.tokenSlice(head);
    // `const Alias = Node;` names the very declaration `Node` does, and
    // the model indexes struct/union/enum/opaque declarations only — an
    // alias is not one of them, so a head written through one resolved
    // to nothing and the callee behind it was never opened.  The alias is
    // followed from its own initializer, as many steps as it is written
    // and no further.
    if (resolveLocalType(model, tree, name, 0)) |info| {
        return .{ .tree = model.tree, .info = info };
    }
    const resolved = cache.importedTypeAcrossImports(&.{name}) orelse return null;
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
/// `tree` is the admitted root model, never an imported declaration.
fn aliasTargetName(tree: *const Ast, name: []const u8) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    const last = tags.len;
    var t: Ast.TokenIndex = 0;
    while (last - t > 4) : (t += 1) {
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
/// (`source_recv . source_field = { }`, `= .{ }`, `= &.{ }`, or `= .empty`). This
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
    const fn_decl = tokens.enclosingFnDecl(tree, start) orelse return false;
    const body = tokens.bodyOf(tree, fn_decl) orelse return false;
    var frames: ReachFrames = .{};
    collectReachFrames(tags, tree.firstToken(body), tree.lastToken(body), &frames);
    var k = start;
    while (k + 4 <= end) : (k += 1) {
        // Pattern: identifier(source_recv) . identifier(source_field) = { }
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), source_recv)) continue;
        if (k + 1 > end or tags[k + 1] != .period) continue;
        if (k + 2 > end or tags[k + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k + 2), source_field)) continue;
        if (k + 3 > end or tags[k + 3] != .equal) continue;
        // A deferred reset does not execute at this copy. In particular,
        // errdefer cannot disarm the source of a successful return.
        if (deferredCall(tree, k)) continue;
        // Cleanup on an earlier exit can still observe both copies.
        // Written-after is not proof that the reset executes first.
        const can_exit = blk: {
            var prior = start;
            while (prior < k) : (prior += 1) {
                switch (tags[prior]) {
                    .keyword_try, .keyword_return, .keyword_break, .keyword_continue => break :blk true,
                    else => {},
                }
            }
            break :blk false;
        };
        if (can_exit) continue;
        if (!reachesCopy(&frames, k, start)) continue;
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
            .ampersand => {
                // A slice reset must be exactly the address of an empty
                // literal, not another allocated or nonempty slice.
                if (k + 8 > end or tags[k + 5] != .period or
                    tags[k + 6] != .l_brace or tags[k + 7] != .r_brace or
                    tags[k + 8] != .semicolon) continue;
                return true;
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


/// True iff the call whose receiver starts at `call` sits inside a
/// `defer` / `errdefer` statement, whatever that statement wraps.
/// Whatever the `defer` is written directly over — a block, an `if` with
/// a condition of its own, another `defer` — its own extent decides,
/// so `defer source.ref.retain();` and `defer if (cond)
/// source.ref.retain();` are one verdict and neither is decided by the
/// token that happens to precede the receiver.
/// Acquire checks operate only on the root copy body admitted by `check`.
fn deferredCall(tree: *const Ast, call: Ast.TokenIndex) bool {
    if (tree.tokens.len == 0 or call == 0) return false;
    const tags = tree.tokens.items(.tag);
    const last = tree.lastToken(.root);
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
        .start = try Pos.fromTokenStart(tree, field_tok),
        .end = try Pos.fromTokenEnd(tree, field_tok),
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
        "`{s}` is copied by value out of a by-value parameter of type `{s}` without acquiring a second reference — `{s}.{s}` releases its `.{s}` field, and the additional uses or cleanup of the handle prevent proving a single ownership handoff; overlapping cleanup can double-free the shared object or SIGFPE; {s}",
        .{ source, type_name, type_name, owned.method, owned.field, fix },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, source_tok),
        .end = try Pos.fromTokenEnd(tree, source_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "ref-counted-copy-without-dupe: by-value ownership handoffs have no implicit destructor" {
    try testing.expectNoFire(check,
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    fn release(self: *Snapshot) void { self.refs.* -= 1; }
        \\};
        \\const Usage = struct {
        \\    scope: *Snapshot,
        \\    fn deinit(self: *Usage) void { self.scope.release(); }
        \\};
        \\fn handoff(source: Usage) Usage { return source; }
        \\fn record(source: Usage, sink: anytype) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    try sink.append(usage);
        \\}
    );
}

test "ref-counted-copy-without-dupe: successful transfers disarm all three error cleanups" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Scope = struct {
        \\    allocator: std.mem.Allocator,
        \\    refs: std.ArrayList(usize) = .empty,
        \\    fn fresh(allocator: std.mem.Allocator) Scope { return .{ .allocator = allocator }; }
        \\    fn deinit(self: *Scope) void { self.refs.deinit(self.allocator); }
        \\};
        \\const Render = struct {
        \\    scope: Scope,
        \\    allocator: std.mem.Allocator,
        \\    fn fresh(allocator: std.mem.Allocator) Render { return .{ .scope = Scope.fresh(allocator), .allocator = allocator }; }
        \\    fn deinit(self: *Render) void { self.scope.deinit(); }
        \\};
        \\const Indirect = struct {
        \\    allocator: std.mem.Allocator,
        \\    draws: std.ArrayList(usize) = .empty,
        \\    fn fresh(allocator: std.mem.Allocator) Indirect { return .{ .allocator = allocator }; }
        \\    fn deinit(self: *Indirect) void { self.draws.deinit(self.allocator); }
        \\};
        \\const Compute = struct {
        \\    allocator: std.mem.Allocator,
        \\    dispatch_usages: std.ArrayList(usize) = .empty,
        \\    fn fresh(allocator: std.mem.Allocator) Compute { return .{ .allocator = allocator }; }
        \\    fn deinit(self: *Compute) void { self.dispatch_usages.deinit(self.allocator); }
        \\};
        \\fn render(source: Render, indirect: Indirect, sink: anytype) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    var metadata = indirect;
        \\    errdefer metadata.deinit();
        \\    try sink.validate();
        \\    try sink.append(usage);
        \\    usage = Render.fresh(usage.allocator);
        \\    try sink.append(metadata);
        \\    metadata = Indirect.fresh(metadata.allocator);
        \\    try sink.commit();
        \\}
        \\fn compute(source: Compute, sink: anytype) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    try sink.append(usage);
        \\    usage = Compute.fresh(usage.allocator);
        \\    try sink.commit();
        \\}
    );
}

test "ref-counted-copy-without-dupe: a later error cannot clean an already transferred handle" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Usage = struct {
        \\    allocator: std.mem.Allocator,
        \\    draws: std.ArrayList(usize) = .empty,
        \\    fn deinit(self: *Usage) void { self.draws.deinit(self.allocator); }
        \\};
        \\const Sink = struct {
        \\    held: Usage,
        \\    fn append(self: *Sink, value: Usage) !void { self.held = value; }
        \\    fn commit(_: *Sink) !void { return error.Failed; }
        \\    fn deinit(self: *Sink) void { self.held.deinit(); }
        \\};
        \\fn record(source: Usage, sink: *Sink) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    try sink.append(usage);
        \\    try sink.commit();
        \\}
    );
}

test "ref-counted-copy-without-dupe: conditional and late resets leave source-proved published ownership" {
    const prelude =
        \\const std = @import("std");
        \\const Usage = struct {
        \\    allocator: std.mem.Allocator,
        \\    draws: std.ArrayList(usize) = .empty,
        \\    fn fresh(allocator: std.mem.Allocator) Usage { return .{ .allocator = allocator }; }
        \\    fn deinit(self: *Usage) void { self.draws.deinit(self.allocator); }
        \\};
        \\const Sink = struct {
        \\    held: Usage,
        \\    fn append(self: *Sink, value: Usage) !void { self.held = value; }
        \\    fn commit(_: *Sink) !void { return error.Failed; }
        \\    fn deinit(self: *Sink) void { self.held.deinit(); }
        \\};
        \\extern fn unknownReset(allocator: std.mem.Allocator) Usage;
    ;
    try testing.expectFiresTyped(check, R, prelude ++
        \\fn record(source: Usage, sink: *Sink, condition: bool) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    try sink.append(usage);
        \\    if (condition) usage = Usage.fresh(usage.allocator);
        \\    try sink.commit();
        \\}
    );
    try testing.expectFiresTyped(check, R, prelude ++
        \\fn record(source: Usage, sink: *Sink) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    try sink.append(usage);
        \\    try sink.commit();
        \\    usage = Usage.fresh(usage.allocator);
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\fn record(source: Usage, sink: *Sink) !void {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    try sink.append(usage);
        \\    usage = unknownReset(usage.allocator);
        \\    try sink.commit();
        \\}
    );
}

test "ref-counted-copy-without-dupe: explicit source cleanup still duplicates ownership" {
    try testing.expectFires(check, R,
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    fn release(self: *Snapshot) void { self.refs.* -= 1; }
        \\};
        \\const Usage = struct {
        \\    scope: *Snapshot,
        \\    fn deinit(self: *Usage) void { self.scope.release(); }
        \\};
        \\fn duplicate(source: Usage) Usage {
        \\    defer source.scope.release();
        \\    return source;
        \\}
    );
}

test "ref-counted-copy-without-dupe: unconditional local cleanup cannot accompany a handoff" {
    try testing.expectFires(check, R,
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    fn release(self: *Snapshot) void { self.refs.* -= 1; }
        \\};
        \\const Usage = struct {
        \\    scope: *Snapshot,
        \\    fn deinit(self: *Usage) void { self.scope.release(); }
        \\};
        \\fn duplicate(source: Usage) Usage {
        \\    var usage = source;
        \\    defer usage.deinit();
        \\    return usage;
        \\}
    );
}

test "ref-counted-copy-without-dupe: repeated error cleanup remains a double teardown" {
    try testing.expectFires(check, R,
        \\const Snapshot = struct {
        \\    refs: *usize,
        \\    fn release(self: *Snapshot) void { self.refs.* -= 1; }
        \\};
        \\const Usage = struct {
        \\    scope: *Snapshot,
        \\    fn deinit(self: *Usage) void { self.scope.release(); }
        \\};
        \\fn duplicate(source: Usage) !Usage {
        \\    var usage = source;
        \\    errdefer usage.deinit();
        \\    errdefer usage.deinit();
        \\    return error.Failure;
        \\}
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


// ── Whole-value copies of an owning handle ─────────────────────────
//
// A by-value parameter has no implicit destructor. Whole copies need a
// source-proved overlapping cleanup or owning publication, not merely an
// owning source declaration. The fixtures below exercise those obligations.

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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&lease).release();
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
        \\    defer @constCast(&source).deref();
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

test "ref-counted-copy-without-dupe: a whole copy that acquires only the second-declared owning field is reported" {
    // An acquire on ONE of the declaration's references balances one
    // owner, not two.  `source.tail.retain()` leaves `ref` — the field
    // this declaration declares first, and the one an acquire on the
    // first field would have balanced — duplicated, so the copy is
    // still reported.
    const src = two_owners_ref_first ++
        \\pub fn copy(source: Shared) Shared {
        \\    defer @constCast(&source).deref(undefined);
        \\    defer @constCast(&source).drop(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
        \\    defer @constCast(&source).drop(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
        \\    defer @constCast(&source).drop(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
        \\    defer @constCast(&source).drop(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
        \\    defer @constCast(&source).drop(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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


test "ref-counted-copy-without-dupe: a whole copy whose teardown is forwarded says it cannot read it" {
    // The same declaration read through the whole-value pass, where the
    // finding may name what balances the copy.  What the callee shows
    // here is not a teardown of either side it was given, so the
    // finding must not claim the reference is one the teardown takes
    // apart — that claim is the reading this disposition replaced.  It
    // stays charged either way; only the reason is unread.
    const src = forwarded_free_owner ++
        \\pub fn copy(source: Holder) Holder {
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deinit();
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
        \\    defer @constCast(&source).deinit();
        \\    return source;
        \\}
        \\
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
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
        \\    defer @constCast(&source).teardown(undefined);
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
        \\    defer @constCast(&source).teardown(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
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
        \\    defer @constCast(&source).deref(undefined);
        \\    {
        \\        source.ref.retain();
        \\    }
        \\    return source;
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
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
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

test "ref-counted-copy-without-dupe: allocator capability used for a temporary free is copied by value" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Oracle = struct {
        \\    capability: std.mem.Allocator,
        \\    fn itemsPath(self: *Oracle) ![]u8 {
        \\        const path = try self.capability.dupe(u8, "path");
        \\        errdefer self.capability.free(path);
        \\        return path;
        \\    }
        \\};
        \\pub fn copy(source: Oracle) Oracle {
        \\    return .{ .capability = source.capability };
        \\}
    );
}

test "ref-counted-copy-without-dupe: an optional allocator descriptor is still owned when destroyed" {
    const src =
        \\const std = @import("std");
        \\const Owner = struct {
        \\    descriptor: ?*std.mem.Allocator,
        \\    capability: std.mem.Allocator,
        \\    fn deinit(self: *Owner) void {
        \\        if (self.descriptor != null) self.capability.destroy(self.descriptor.?);
        \\    }
        \\};
        \\pub fn copy(source: Owner) Owner { defer @constCast(&source).deinit(); return source; }
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, src);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`.descriptor`") != null);
}

test "ref-counted-copy-without-dupe: address of empty slice disarms a moved buffer" {
    const prefix =
        \\const std = @import("std");
        \\const Owner = struct {
        \\    owned: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Owner) void {
        \\        if (self.owned.len != 0) self.allocator.free(self.owned);
        \\    }
        \\};
    ;
    try testing.expectNoFire(check, prefix ++
        \\fn move(allocator: std.mem.Allocator) !Owner {
        \\    var expanded: Owner = .{ .owned = try allocator.alloc(u8, 4), .allocator = allocator };
        \\    errdefer expanded.deinit();
        \\    const pending: Owner = .{ .owned = expanded.owned, .allocator = expanded.allocator };
        \\    expanded.owned = &.{};
        \\    return pending;
        \\}
    );
    try testing.expectFires(check, R, prefix ++
        \\fn copy(expanded: *Owner, clear: bool) Owner {
        \\    const pending: Owner = .{ .owned = expanded.owned, .allocator = expanded.allocator };
        \\    if (clear) expanded.owned = &.{};
        \\    return pending;
        \\}
    );
    try testing.expectFires(check, R, prefix ++
        \\fn copy(expanded: *Owner) Owner {
        \\    const pending: Owner = .{ .owned = expanded.owned, .allocator = expanded.allocator };
        \\    expanded.owned = &.{1};
        \\    return pending;
        \\}
    );
}

test "ref-counted-copy-without-dupe: foreign mixed teardown preserves allocator capability identity" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const foreign = @import("context.zig");
        \\fn copy(old: foreign.Context) foreign.Context {
        \\    return .{ .allocator = old.allocator };
        \\}
    ;
    const foreign: [:0]const u8 =
        \\const std = @import("std");
        \\pub const Context = struct {
        \\    allocator: std.mem.Allocator,
        \\    words: std.ArrayList(u8),
        \\    buffer: ?[]u8,
        \\    fn deinit(self: *Context) void {
        \\        self.words.deinit(self.allocator);
        \\        if (self.buffer) |bytes| self.allocator.free(bytes);
        \\    }
        \\};
        \\pub const OwnedDescriptor = struct {
        \\    allocator: *std.mem.Allocator,
        \\    capability: std.mem.Allocator,
        \\    fn deinit(self: *OwnedDescriptor) void { self.capability.destroy(self.allocator); }
        \\};
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var foreign_tree = try Ast.parse(gpa, foreign, .zig);
    defer foreign_tree.deinit(gpa);
    var cache = file_cache_mod.FileCache.init(gpa, &tree);
    defer cache.deinit();
    var foreign_cache = file_cache_mod.FileCache.init(gpa, &foreign_tree);
    defer foreign_cache.deinit();
    const model = try foreign_cache.fileModel();
    const context: DestType = .{ .tree = &foreign_tree, .info = model.findType("Context").? };
    try std.testing.expect((try verdictOnField(&cache, context, "allocator")) == .borrowed);
    const descriptor: DestType = .{ .tree = &foreign_tree, .info = model.findType("OwnedDescriptor").? };
    const verdict = try verdictOnField(&cache, descriptor, "allocator");
    try std.testing.expect(verdict == .owned);
    try std.testing.expectEqual(Payload.destroyed_argument, verdict.owned);
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "context.zig", .data = foreign });
    try tmp.dir.writeFile(io, .{ .sub_path = "capability.zig", .data = source });
    try tmp.dir.writeFile(io, .{ .sub_path = "descriptor.zig", .data =
        \\const foreign = @import("context.zig");
        \\fn copy(old: foreign.OwnedDescriptor) foreign.OwnedDescriptor {
        \\    return .{ .allocator = old.allocator, .capability = old.capability };
        \\}
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    const cases = .{ .{ "capability.zig", @as(usize, 0) }, .{ "descriptor.zig", @as(usize, 1) } };
    inline for (cases) |case| {
        const path = try std.fs.path.join(gpa, &.{ directory, case[0] });
        defer gpa.free(path);
        const bytes = try std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(1 << 20));
        defer gpa.free(bytes);
        const src_z = try gpa.dupeSentinel(u8, bytes, 0);
        defer gpa.free(src_z);
        var caller_tree = try Ast.parse(gpa, src_z, .zig);
        defer caller_tree.deinit(gpa);
        var caller_cache = file_cache_mod.FileCache.init(gpa, &caller_tree);
        defer caller_cache.deinit();
        caller_cache.setProject(&project, path);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer testing.freeProblems(gpa, &problems);
        try check(gpa, &caller_tree, &caller_cache, &config_mod.Default, &problems);
        try std.testing.expectEqual(case[1], problems.items.len);
        for (problems.items) |problem| try std.testing.expectEqualStrings(R, problem.rule_id);
    }
}

test "refcount source admission preserves count boundaries without narrowing" {
    const max = std.math.maxInt(u32);
    try std.testing.expectEqual(max, try admittedTokenCount(max - 1, max, max));
    try std.testing.expectError(error.SourceTooWide, admittedTokenCount(max, 1, 1));
    if (@bitSizeOf(usize) > 32) {
        const beyond: usize = @as(usize, max) + 1;
        try std.testing.expectError(error.SourceTooWide, admittedTokenCount(1, beyond, 1));
        try std.testing.expectError(error.SourceTooWide, admittedTokenCount(1, 1, beyond));
    }
}

const slice_handoff_prelude =
    \\const std = @import("std");
    \\const Buffer = struct {
    \\    indexes: []u32,
    \\    count: usize = 0,
    \\    fn acquire(gpa: std.mem.Allocator) !Buffer { return .{ .indexes = try gpa.alloc(u32, 4) }; }
    \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
    \\    fn finish(self: *Buffer) !void {
    \\        if (self.count >= self.indexes.len) return error.Full;
    \\        self.indexes[self.count] = 0;
    \\    }
    \\};
    \\const Output = struct {
    \\    indexes: []u32,
    \\    count: usize = 0,
    \\    fn deinit(self: *Output, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
    \\};
    \\
;

test "ref-counted-copy-without-dupe: a fresh slice wrapper transfers on success only" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    try source.finish();
        \\    return .{ .indexes = source.indexes, .count = source.count };
        \\}
    );
}

test "ref-counted-copy-without-dupe: a temporary slice wrapper never tears down the owner's slice" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\pub fn finish(source: *Output) !void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    try temporary.finish();
        \\}
    );
}

test "ref-counted-copy-without-dupe: optional take removes the owning slot before the slice handoff" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\const Owner = struct {
        \\    slot: ?Buffer,
        \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.slot) |*slot| slot.deinit(gpa);
        \\    }
        \\    fn take(self: *Owner) Output {
        \\        const source = self.slot.?;
        \\        self.slot = null;
        \\        return .{ .indexes = source.indexes };
        \\    }
        \\};
    );
}

test "ref-counted-copy-without-dupe: unconditional source teardown overlaps slice return" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    defer source.deinit(gpa);
        \\    return .{ .indexes = source.indexes };
        \\}
    );
}

test "ref-counted-copy-without-dupe: temporary slice teardown duplicates the owner" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\pub fn finish(source: *Output, gpa: std.mem.Allocator) !void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    defer temporary.deinit(gpa);
        \\    try temporary.finish();
        \\}
    );
}

test "ref-counted-copy-without-dupe: error cleanup on both slice wrappers overlaps" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    var result: Output = .{ .indexes = source.indexes };
        \\    errdefer result.deinit(gpa);
        \\    try source.finish();
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: an optional owner kept live still duplicates its slice" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\const Owner = struct {
        \\    slot: ?Buffer,
        \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.slot) |*slot| slot.deinit(gpa);
        \\    }
        \\    fn take(self: *Owner) Output {
        \\        const source = self.slot.?;
        \\        return .{ .indexes = source.indexes };
        \\    }
        \\};
    );
}

test "ref-counted-copy-without-dupe: opaque source calls with proved cleanup still overlap" {
    // An unread helper alone was the old, invalid reporting oracle.
    // The unconditional cleanup now proves the overlap independently.
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\extern fn observe(source: *Buffer) void;
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    observe(&source);
        \\    defer source.deinit(gpa);
        \\    return .{ .indexes = source.indexes };
        \\}
    );
}

/// Assert an unsafe ownership use, not the number of aliases the rule reports.
fn expectOwnershipOverlap(src: []const u8, use: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check, src);
    defer testing.freeProblems(gpa, &problems);
    const first = std.mem.indexOf(u8, src, use) orelse return error.MissingOwnershipUse;
    for (problems.items) |problem| {
        if (std.mem.eql(u8, problem.rule_id, R) and
            problem.start.byte >= first and problem.start.byte < first + use.len) return;
    }
    return error.MissingOwnershipOverlap;
}

test "ref-counted-copy-without-dupe: a second returned slice alias is not a single handoff" {
    try expectOwnershipOverlap(slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator) !struct { first: Output, second: Output } {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    return .{
        \\        .first = .{ .indexes = source.indexes },
        \\        .second = .{ .indexes = source.indexes },
        \\    };
        \\}
    , ".second = .{ .indexes = source.indexes }");
}

test "ref-counted-copy-without-dupe: error-only source cleanup stays disjoint from a local returned slice owner" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    const result: Output = .{ .indexes = source.indexes };
        \\    try source.finish();
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: a slice temporary method that frees cannot masquerade as finish" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    indexes: []u32,
        \\    fn finish(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
        \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
        \\};
        \\const Output = struct {
        \\    indexes: []u32,
        \\    fn deinit(self: *Output, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
        \\};
        \\pub fn finish(source: *Output, gpa: std.mem.Allocator) void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    temporary.finish(gpa);
        \\}
    );
}

test "ref-counted-copy-without-dupe: opaque temporary calls with proved cleanup still overlap" {
    // Unknown helper effects cannot establish an owning temporary.
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\extern fn observe(temporary: *Buffer) void;
        \\pub fn finish(source: *Output, gpa: std.mem.Allocator) void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    observe(&temporary);
        \\    defer temporary.deinit(gpa);
        \\}
    );
}

test "ref-counted-copy-without-dupe: conditional or restored optional slots retain slice ownership" {
    inline for (.{
        "if (clear) self.slot = null;",
        "self.slot = null; self.slot = source;",
    }) |reset| {
        try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
            \\const Owner = struct {
            \\    slot: ?Buffer,
            \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
            \\        if (self.slot) |*slot| slot.deinit(gpa);
            \\    }
            \\    fn take(self: *Owner, clear: bool) Output {
            \\        const source = self.slot.?;
            \\
        ++ reset ++
            \\
            \\        return .{ .indexes = source.indexes };
            \\    }
            \\};
        );
    }
}

const argument_view_prelude =
    \\const std = @import("std");
    \\const Data = struct {
    \\    bytes: []u8,
    \\    fn deinit(self: *Data, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
    \\};
    \\const Plan = struct {
    \\    data: *Data,
    \\    fn deinit(self: *Plan, gpa: std.mem.Allocator) void {
    \\        self.data.deinit(gpa);
    \\        gpa.destroy(self.data);
    \\    }
    \\};
    \\const View = struct { data: ?*const Data = null };
    \\
;

test "ref-counted-copy-without-dupe: anonymous borrowed view argument uses its callee parameter" {
    try testing.expectNoFireTyped(check, argument_view_prelude ++
        \\fn emit(gpa: std.mem.Allocator, view: View) ![]u8 {
        \\    return gpa.dupe(u8, view.data.?.bytes);
        \\}
        \\pub fn borrow(gpa: std.mem.Allocator, plan: *const Plan) ![]u8 {
        \\    return emit(gpa, .{ .data = plan.data });
        \\}
    );
}

test "ref-counted-copy-without-dupe: method argument destination accounts for the implicit receiver" {
    try testing.expectNoFireTyped(check, argument_view_prelude ++
        \\const Emitter = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn emit(self: *const Emitter, marker: u32, view: View) ![]u8 {
        \\        _ = marker;
        \\        return self.gpa.dupe(u8, view.data.?.bytes);
        \\    }
        \\};
        \\pub fn borrow(emitter: *const Emitter, plan: *const Plan) ![]u8 {
        \\    return emitter.emit(1, .{ .data = plan.data });
        \\}
    );
}

test "ref-counted-copy-without-dupe: qualified static callee does not skip its first parameter" {
    try testing.expectNoFireTyped(check, argument_view_prelude ++
        \\const Emitter = struct {
        \\    fn emit(view: View, marker: u32) usize {
        \\        _ = marker;
        \\        return view.data.?.bytes.len;
        \\    }
        \\};
        \\pub fn borrow(plan: *const Plan) usize {
        \\    return Emitter.emit(.{ .data = plan.data }, 1);
        \\}
    );
}

test "ref-counted-copy-without-dupe: an owning argument destination retains its cleanup obligation" {
    try testing.expectFiresTyped(check, R, argument_view_prelude ++
        \\fn consume(gpa: std.mem.Allocator, owned: Plan) void {
        \\    var value = owned;
        \\    value.deinit(gpa);
        \\}
        \\pub fn copy(gpa: std.mem.Allocator, plan: *const Plan) void {
        \\    consume(gpa, .{ .data = plan.data });
        \\}
    );
}


test "ref-counted-copy-without-dupe: a nested argument literal cannot inherit the outer view type" {
    try testing.expectFiresTyped(check, R, argument_view_prelude ++
        \\const Envelope = struct { nested: Plan };
        \\fn emit(value: Envelope) void { _ = value; }
        \\pub fn copy(plan: *const Plan) void {
        \\    emit(.{ .nested = .{ .data = plan.data } });
        \\}
    );
}

const whole_handoff_owner =
    \\const std = @import("std");
    \\const Buffer = struct {
    \\    bytes: []u8 = &.{},
    \\    count: usize = 0,
    \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
    \\    fn extract(self: *Buffer) Buffer {
    \\        const result = self.*;
    \\        self.* = .{};
    \\        return result;
    \\    }
    \\};
;

test "ref-counted-copy-without-dupe: scalar reads do not duplicate the sole local owner" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\pub fn consume(gpa: std.mem.Allocator, source: Buffer) usize {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return owned.count;
        \\}
    );
}

test "ref-counted-copy-without-dupe: a structurally disarming method permits deferred cleanup" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\pub fn transfer(gpa: std.mem.Allocator, source: Buffer) Buffer {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return owned.extract();
        \\}
    );
}

test "ref-counted-copy-without-dupe: nested disarming move and in-place append retain one local owner" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Environment = struct {
        \\    values: std.ArrayList(u8) = .empty,
        \\    fn extract(self: *Environment) Environment { const result = self.*; self.* = .{}; return result; }
        \\    fn deinit(self: *Environment, gpa: std.mem.Allocator) void { self.values.deinit(gpa); self.* = undefined; }
        \\};
        \\const Path = struct {
        \\    env: Environment,
        \\    fn extract(self: *Path) Path { return .{ .env = self.env.extract() }; }
        \\    fn deinit(self: *Path, gpa: std.mem.Allocator) void { self.env.deinit(gpa); self.* = undefined; }
        \\};
        \\pub fn consume(gpa: std.mem.Allocator, path: Path) !void {
        \\    var owned = path;
        \\    defer owned.deinit(gpa);
        \\    try owned.env.values.append(gpa, 1);
        \\}
        \\pub fn transfer(gpa: std.mem.Allocator, path: Path) !Path {
        \\    var owned = path;
        \\    errdefer owned.deinit(gpa);
        \\    try owned.env.values.append(gpa, 1);
        \\    return owned.extract();
        \\}
    );
}

test "ref-counted-copy-without-dupe: non-disarming move is proved overlap but opaque returns are unknown" {
    try testing.expectFiresTyped(check, R, whole_handoff_owner ++
        \\fn move(source: *Buffer) Buffer { return source.*; }
        \\pub fn duplicate(gpa: std.mem.Allocator, source: Buffer) Buffer {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return move(&owned);
        \\}
    );
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\pub fn duplicate(gpa: std.mem.Allocator, source: Buffer, transform: *const fn (*Buffer) Buffer) Buffer {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return transform(&owned);
        \\}
    );
}

test "ref-counted-copy-without-dupe: a cleared move result cannot hide overlapping parameter cleanup" {
    try testing.expectFiresTyped(check, R, whole_handoff_owner ++
        \\pub fn duplicate(gpa: std.mem.Allocator, source: Buffer) Buffer {
        \\    defer @constCast(&source).deinit(gpa);
        \\    var owned = source;
        \\    return owned.extract();
        \\}
    );
}

test "ref-counted-copy-without-dupe: orelse return and later transfer have exclusive ownership" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\fn transform(source: Buffer) Buffer { return source; }
        \\pub fn choose(source: Buffer, change: ?u32) Buffer {
        \\    const node = change orelse return source;
        \\    _ = node;
        \\    return transform(source);
        \\}
    );
    try expectOwnershipOverlap(whole_handoff_owner ++
        \\fn transform(source: Buffer) Buffer { return source; }
        \\pub fn choose(gpa: std.mem.Allocator, source: Buffer, change: ?u32) Buffer {
        \\    defer @constCast(&source).deinit(gpa);
        \\    const node = change orelse return source;
        \\    _ = node;
        \\    return transform(source);
        \\}
    , "const node = change orelse return source;");
}

test "ref-counted-copy-without-dupe: imported argument destination retains its declaring scope" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "emitter.zig", .data =
        \\const std = @import("std");
        \\pub const Data = struct { bytes: []u8 };
        \\pub const View = struct { data: ?*const Data = null };
        \\pub const Owner = struct {
        \\    data: *Data,
        \\    pub fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.data.bytes);
        \\        gpa.destroy(self.data);
        \\    }
        \\};
        \\pub fn emit(gpa: std.mem.Allocator, view: View) ![]u8 {
        \\    return gpa.dupe(u8, view.data.?.bytes);
        \\}
        \\pub fn consume(gpa: std.mem.Allocator, owner: Owner) void {
        \\    var value = owner;
        \\    value.deinit(gpa);
        \\}
    });
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const emitter = @import("emitter.zig");
        \\const View = struct {
        \\    data: *emitter.Data,
        \\    fn deinit(self: *View, gpa: std.mem.Allocator) void { gpa.destroy(self.data); }
        \\};
        \\const Owner = struct { data: ?*const emitter.Data };
        \\const Plan = struct {
        \\    data: *emitter.Data,
        \\    fn deinit(self: *Plan, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.data.bytes);
        \\        gpa.destroy(self.data);
        \\    }
        \\};
        \\pub fn borrow(gpa: std.mem.Allocator, plan: *const Plan) ![]u8 {
        \\    return emitter.emit(gpa, .{ .data = plan.data });
        \\}
        \\pub fn duplicate(gpa: std.mem.Allocator, plan: *const Plan) void {
        \\    emitter.consume(gpa, .{ .data = plan.data });
        \\}
    ;
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "caller.zig" });
    defer gpa.free(path);
    try tmp.dir.writeFile(io, .{ .sub_path = "caller.zig", .data = source });
    const type_engine = @import("type_engine");
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: type_engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    project.type_context = &context;
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.setProject(&project, path);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expect(problems.items.len != 0);
    const owned_copy = std.mem.indexOf(u8, source, "emitter.consume(gpa, .{").?;
    var line: u32 = 1;
    for (source[0..owned_copy]) |byte| {
        if (byte == '\n') line += 1;
    }
    for (problems.items) |problem| {
        try std.testing.expectEqualStrings(R, problem.rule_id);
        try std.testing.expectEqual(line, problem.start.line);
        try std.testing.expect(std.mem.indexOf(u8, problem.message, "`.data`") != null);
    }
}

test "ref-counted-copy-without-dupe: borrowed source cannot replace an owning argument destination" {
    try testing.expectFiresTyped(check, R, argument_view_prelude ++
        \\const ReadOnly = struct { data: *Data };
        \\fn consume(gpa: std.mem.Allocator, owned: Plan) void {
        \\    var value = owned;
        \\    value.deinit(gpa);
        \\}
        \\pub fn copy(gpa: std.mem.Allocator, source: *const ReadOnly) void {
        \\    consume(gpa, .{ .data = source.data });
        \\}
    );
}

test "ref-counted-copy-without-dupe: nested transfer clears an optional owning field before returning it" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\const Path = struct {
        \\    env: Buffer,
        \\    state: ?*u8 = null,
        \\    fn extract(self: *Path) Path {
        \\        const saved = self.state;
        \\        self.state = null;
        \\        return .{ .env = self.env.extract(), .state = saved };
        \\    }
        \\    fn deinit(self: *Path, gpa: std.mem.Allocator) void {
        \\        self.env.deinit(gpa);
        \\        if (self.state) |state| gpa.destroy(state);
        \\    }
        \\};
        \\pub fn transfer(gpa: std.mem.Allocator, source: Path) Path {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return owned.extract();
        \\}
    );
}

test "ref-counted-copy-without-dupe: in-place method spelling cannot hide a second free" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn append(self: *Buffer, gpa: std.mem.Allocator, value: u8) void {
        \\        _ = value;
        \\        gpa.free(self.bytes);
        \\    }
        \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\pub fn consume(gpa: std.mem.Allocator, source: Buffer) void {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    owned.append(gpa, 1);
        \\}
    );
}

test "ref-counted-copy-without-dupe: a move that leaves one nested owner live still fires" {
    try expectOwnershipOverlap(whole_handoff_owner ++
        \\const Pair = struct {
        \\    first: Buffer,
        \\    second: Buffer,
        \\    fn extract(self: *Pair) Pair {
        \\        return .{ .first = self.first.extract(), .second = self.second };
        \\    }
        \\    fn deinit(self: *Pair, gpa: std.mem.Allocator) void {
        \\        self.first.deinit(gpa);
        \\        self.second.deinit(gpa);
        \\    }
        \\};
        \\pub fn transfer(gpa: std.mem.Allocator, source: Pair) Pair {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return owned.extract();
        \\}
    , "return .{ .first = self.first.extract(), .second = self.second };");
}


test "ref-counted-copy-without-dupe: orelse return excludes a later call assigned to a local" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\fn transform(source: Buffer, node: u32) Buffer { _ = node; return source; }
        \\pub fn choose(gpa: std.mem.Allocator, source: Buffer, change: ?u32) ?Buffer {
        \\    const node = change orelse return source;
        \\    var outcome = transform(source, node);
        \\    defer outcome.deinit(gpa);
        \\    return null;
        \\}
    );
    try testing.expectFiresTyped(check, R, whole_handoff_owner ++
        \\fn transform(source: Buffer, node: u32) Buffer { _ = node; return source; }
        \\pub fn choose(gpa: std.mem.Allocator, source: Buffer, change: ?u32) ?Buffer {
        \\    const node = change orelse return source;
        \\    var first = transform(source, node);
        \\    defer first.deinit(gpa);
        \\    var second = transform(source, node);
        \\    defer second.deinit(gpa);
        \\    return null;
        \\}
    );
}

test "ref-counted-copy-without-dupe: an error deferred empty reset does not disarm a successful copy" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\pub fn copy(source: *Buffer) !Buffer {
        \\    const result: Buffer = .{ .bytes = source.bytes };
        \\    errdefer source.bytes = &.{};
        \\    return result;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\pub fn take(source: *Buffer) Buffer {
        \\    const result: Buffer = .{ .bytes = source.bytes };
        \\    source.bytes = &.{};
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: deferred value reset is not an immediate transfer" {
    try testing.expectFires(check, R,
        \\const Ref = struct { fn deinit(self: *Ref) void { _ = self; } };
        \\const Owner = struct {
        \\    ref: Ref,
        \\    fn deinit(self: *Owner) void { self.ref.deinit(); }
        \\};
        \\fn copy(source: *Owner) Owner {
        \\    const result: Owner = .{ .ref = source.ref };
        \\    defer source.ref = .{};
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: fallible exit before empty reset retains duplicate cleanup" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Owner) void { if (self.bytes.len != 0) self.gpa.free(self.bytes); }
        \\};
        \\fn maybeFail(fail: bool) !void { if (fail) return error.Bad; }
        \\pub fn copy(source: *Owner, fail: bool) !Owner {
        \\    errdefer source.deinit();
        \\    var result: Owner = .{ .bytes = source.bytes, .gpa = source.gpa };
        \\    errdefer result.deinit();
        \\    try maybeFail(fail);
        \\    source.bytes = &.{};
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: a complete no-free slice method may still publish a second owner" {
    inline for (.{ "", "self.indexes[0] = 0;" }) |before_publish| {
        try testing.expectFiresTyped(check, R,
            \\const std = @import("std");
            \\const Output = struct {
            \\    indexes: []u32,
            \\    fn deinit(self: *Output, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
            \\};
            \\var published: Output = undefined;
            \\const Buffer = struct {
            \\    indexes: []u32,
            \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
            \\    fn publish(self: *Buffer, fail: bool) !void {
            \\
        ++ before_publish ++
            \\
            \\        published.indexes = self.indexes;
            \\        if (fail) return error.Bad;
            \\    }
            \\};
            \\pub fn duplicate(source: *Output, fail: bool) !void {
            \\    var temporary: Buffer = .{ .indexes = source.indexes };
            \\    try temporary.publish(fail);
            \\}
        );
    }
}

test "ref-counted-copy-without-dupe: an aliased optional owner preserves a second snapshot cleanup" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\const Owner = struct {
        \\    slot: ?Buffer,
        \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.slot) |*slot| slot.deinit(gpa);
        \\    }
        \\    fn take(self: *Owner, gpa: std.mem.Allocator) Output {
        \\        const alias = self;
        \\        var duplicate = alias.slot.?;
        \\        defer duplicate.deinit(gpa);
        \\        const source = self.slot.?;
        \\        self.slot = null;
        \\        return .{ .indexes = source.indexes };
        \\    }
        \\};
    );
}

test "ref-counted-copy-without-dupe: one error cleanup call can release the same slice twice" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\fn releaseBoth(a: *Buffer, b: *Buffer, gpa: std.mem.Allocator) void {
        \\    a.deinit(gpa);
        \\    b.deinit(gpa);
        \\}
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer releaseBoth(&source, &source, gpa);
        \\    try source.finish();
        \\    return .{ .indexes = source.indexes };
        \\}
    );
}

test "ref-counted-copy-without-dupe: a deferred optional clear is not a successful take" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\const Owner = struct {
        \\    slot: ?Buffer,
        \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.slot) |*slot| slot.deinit(gpa);
        \\    }
        \\    fn take(self: *Owner) Output {
        \\        const source = self.slot.?;
        \\        errdefer self.slot = null;
        \\        return .{ .indexes = source.indexes };
        \\    }
        \\};
    );
}

test "ref-counted-copy-without-dupe: a read-only scalar result can encode the slice address" {
    // A scalar result's possible address dependency is not a publication
    // certificate. Keep this unsafe case grounded in an explicit cleanup.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Output = struct {
        \\    indexes: []u32,
        \\    fn deinit(self: *Output, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
        \\};
        \\var published_address: usize = 0;
        \\var published: Output = undefined;
        \\const Buffer = struct {
        \\    indexes: []u32,
        \\    fn deinit(self: *Buffer, gpa: std.mem.Allocator) void { gpa.free(self.indexes); }
        \\    fn address(self: *Buffer, fail: bool) !usize {
        \\        if (fail) return error.Bad;
        \\        return @intFromPtr(self.indexes.ptr);
        \\    }
        \\};
        \\pub fn duplicate(source: *Output, fail: bool, gpa: std.mem.Allocator) !void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    defer temporary.deinit(gpa);
        \\    published_address = try temporary.address(fail);
        \\    published.indexes = @as([*]u32, @ptrFromInt(published_address))[0..source.indexes.len];
        \\}
    );
}

test "ref-counted-copy-without-dupe: labeled break cannot skip source disarm" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Owner) void { if (self.bytes.len != 0) self.gpa.free(self.bytes); }
        \\};
        \\pub fn copy(source: *Owner, skip: bool) Owner {
        \\    var result: Owner = undefined;
        \\    blk: {
        \\        result = Owner{ .bytes = source.bytes, .gpa = source.gpa };
        \\        if (skip) break :blk;
        \\        source.bytes = &.{};
        \\    }
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: loop continue cannot skip source disarm" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Owner) void { if (self.bytes.len != 0) self.gpa.free(self.bytes); }
        \\};
        \\pub fn copy(source: *Owner, skip: bool) Owner {
        \\    var result: Owner = undefined;
        \\    for ([_]bool{skip}) |step| {
        \\        result = Owner{ .bytes = source.bytes, .gpa = source.gpa };
        \\        if (step) continue;
        \\        source.bytes = &.{};
        \\    }
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: unknown helper effects do not prove a fresh slice has two owners" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\extern fn observe(source: *Buffer) void;
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    observe(&source);
        \\    try source.finish();
        \\    return .{ .indexes = source.indexes, .count = source.count };
        \\}
    );
}

test "ref-counted-copy-without-dupe: unknown helper cannot hide proved unconditional slice cleanup" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\extern fn observe(source: *Buffer) void;
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    observe(&source);
        \\    defer source.deinit(gpa);
        \\    return .{ .indexes = source.indexes, .count = source.count };
        \\}
    );
}

test "ref-counted-copy-without-dupe: optional take with opaque helper effects stays silent" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\extern fn observe(owner: *Owner) void;
        \\const Owner = struct {
        \\    slot: ?Buffer,
        \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.slot) |*slot| slot.deinit(gpa);
        \\    }
        \\    fn take(self: *Owner) Output {
        \\        observe(self);
        \\        const source = self.slot.?;
        \\        self.slot = null;
        \\        return .{ .indexes = source.indexes, .count = source.count };
        \\    }
        \\};
    );
}

test "ref-counted-copy-without-dupe: optional take with proved snapshot cleanup still reports" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\extern fn observe(owner: *Owner) void;
        \\const Owner = struct {
        \\    slot: ?Buffer,
        \\    fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.slot) |*slot| slot.deinit(gpa);
        \\    }
        \\    fn take(self: *Owner, gpa: std.mem.Allocator) Output {
        \\        observe(self);
        \\        var source = self.slot.?;
        \\        self.slot = null;
        \\        defer source.deinit(gpa);
        \\        return .{ .indexes = source.indexes, .count = source.count };
        \\    }
        \\};
    );
}

test "ref-counted-copy-without-dupe: opaque temporary helper effects do not establish a destructor" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\extern fn observe(temporary: *Buffer) void;
        \\pub fn finish(source: *Output) void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    observe(&temporary);
        \\}
    );
}

test "ref-counted-copy-without-dupe: opaque temporary helper cannot hide a proved destructor" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\extern fn observe(temporary: *Buffer) void;
        \\pub fn finish(source: *Output, gpa: std.mem.Allocator) void {
        \\    var temporary: Buffer = .{ .indexes = source.indexes };
        \\    observe(&temporary);
        \\    defer temporary.deinit(gpa);
        \\}
    );
}

test "ref-counted-copy-without-dupe: freeing another helper argument does not prove source ownership overlap" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\fn finish(source: *Buffer, other: []u32, gpa: std.mem.Allocator) void {
        \\    source.count = 1;
        \\    gpa.free(other);
        \\}
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    const other = try gpa.alloc(u32, 2);
        \\    finish(&source, other, gpa);
        \\    return .{ .indexes = source.indexes, .count = source.count };
        \\}
    );
}

test "ref-counted-copy-without-dupe: a later success path free proves slice ownership overlap" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    const result: Output = .{ .indexes = source.indexes, .count = source.count };
        \\    gpa.free(source.indexes);
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: scalar slice length aliases do not own storage" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\fn size(source: *Output) usize {
        \\    const temporary: Buffer = .{ .indexes = source.indexes };
        \\    const length = temporary.indexes.len;
        \\    return length;
        \\}
    );
}

test "ref-counted-copy-without-dupe: opaque effects cannot hide two overlapping error cleanups" {
    try testing.expectFiresTyped(check, R, slice_handoff_prelude ++
        \\extern fn observe(source: *Buffer) void;
        \\pub fn transfer(gpa: std.mem.Allocator, fail: bool) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    observe(&source);
        \\    errdefer source.deinit(gpa);
        \\    var result: Output = .{ .indexes = source.indexes };
        \\    errdefer result.deinit(gpa);
        \\    if (fail) return error.Bad;
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: error cleanups in completed sibling scopes do not overlap" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\pub fn transfer(gpa: std.mem.Allocator, first: bool) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    if (first) {
        \\        errdefer source.deinit(gpa);
        \\        try source.finish();
        \\    } else {
        \\        errdefer source.deinit(gpa);
        \\        try source.finish();
        \\    }
        \\    return .{ .indexes = source.indexes, .count = source.count };
        \\}
    );
}

test "ref-counted-copy-without-dupe: opaque mutation of the sole consumed handle proves no duplicate owner" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\extern fn mutate(buffer: *Buffer) void;
        \\pub fn consume(gpa: std.mem.Allocator, source: Buffer) void {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    mutate(&owned);
        \\}
    );
}

test "ref-counted-copy-without-dupe: pointer helper arguments do not create implicit owning copies" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\fn write(buffer: *Buffer) void { buffer.count = 1; }
        \\pub fn transfer(gpa: std.mem.Allocator, source: Buffer) Buffer {
        \\    var owned = source;
        \\    errdefer owned.deinit(gpa);
        \\    write(&owned);
        \\    return owned.extract();
        \\}
    );
}

test "ref-counted-copy-without-dupe: a borrowed mutable subfield is not a second environment owner" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Environment = struct {
        \\    values: std.AutoHashMapUnmanaged(u32, u32) = .empty,
        \\    fn move(self: *Environment) Environment { const result = self.*; self.* = .{}; return result; }
        \\    fn deinit(self: *Environment, gpa: std.mem.Allocator) void { self.values.deinit(gpa); }
        \\};
        \\const Path = struct {
        \\    env: Environment,
        \\    state: ?*u8 = null,
        \\    fn move(self: *Path) Path {
        \\        const state = self.state;
        \\        self.state = null;
        \\        return .{ .env = self.env.move(), .state = state };
        \\    }
        \\    fn deinit(self: *Path, gpa: std.mem.Allocator) void {
        \\        self.env.deinit(gpa);
        \\        if (self.state) |state| gpa.destroy(state);
        \\    }
        \\};
        \\fn write(gpa: std.mem.Allocator, env: *Environment) !void { try env.values.put(gpa, 1, 1); }
        \\pub fn transfer(gpa: std.mem.Allocator, source: Path) !Path {
        \\    var owned = source;
        \\    errdefer owned.deinit(gpa);
        \\    try write(gpa, &owned.env);
        \\    return owned.move();
        \\}
    );
}

test "ref-counted-copy-without-dupe: unknown temporary uses cannot borrow its type destructor as an obligation" {
    try testing.expectNoFireTyped(check, slice_handoff_prelude ++
        \\extern fn observe(temporary: *Buffer) void;
        \\pub fn transfer(gpa: std.mem.Allocator) !Output {
        \\    var source = try Buffer.acquire(gpa);
        \\    errdefer source.deinit(gpa);
        \\    var result: Output = .{ .indexes = source.indexes, .count = source.count };
        \\    var temporary: Buffer = .{ .indexes = result.indexes, .count = result.count };
        \\    observe(&temporary);
        \\    try temporary.finish();
        \\    return result;
        \\}
    );
}

test "ref-counted-copy-without-dupe: generic borrowed literal has no declaration-owned destructor" {
    try testing.expectNoFireTyped(check, argument_view_prelude ++
        \\fn emit(view: anytype) usize { return view.data.bytes.len; }
        \\pub fn borrow(plan: *const Plan) usize {
        \\    return emit(.{ .data = plan.data });
        \\}
    );
}

test "ref-counted-copy-without-dupe: a published handle survives until the later error cleanup" {
    try testing.expectFiresTyped(check, R, whole_handoff_owner ++
        \\const Sink = struct {
        \\    held: Buffer,
        \\    fn save(self: *Sink, value: Buffer) void { self.held = value; }
        \\    fn deinit(self: *Sink, gpa: std.mem.Allocator) void { self.held.deinit(gpa); }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer, sink: *Sink) !void {
        \\    var owned = source;
        \\    errdefer owned.deinit(gpa);
        \\    sink.save(owned);
        \\    try fail();
        \\}
    );
}

test "ref-counted-copy-without-dupe: a stored handle without destination cleanup proves no second owner" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\const View = struct {
        \\    held: Buffer,
        \\    fn save(self: *View, value: Buffer) void { self.held = value; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer, view: *View) !void {
        \\    var owned = source;
        \\    errdefer owned.deinit(gpa);
        \\    view.save(owned);
        \\    try fail();
        \\}
    );
}

test "ref-counted-copy-without-dupe: a helper release and local cleanup overlap" {
    try testing.expectFiresTyped(check, R, whole_handoff_owner ++
        \\fn dispose(gpa: std.mem.Allocator, value: *Buffer) void { gpa.free(value.bytes); }
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer) void {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    dispose(gpa, &owned);
        \\}
    );
}

test "ref-counted-copy-without-dupe: freeing another helper argument does not release the handle" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\fn dispose(gpa: std.mem.Allocator, value: *Buffer, other: []u8) void {
        \\    value.count = 1;
        \\    gpa.free(other);
        \\}
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer) !void {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    const other = try gpa.alloc(u8, 1);
        \\    dispose(gpa, &owned, other);
        \\}
    );
}

test "ref-counted-copy-without-dupe: cleanup on a sibling binding is not cleanup on the copied handle" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer) void {
        \\    {
        \\        var owned = source;
        \\        defer owned.deinit(gpa);
        \\    }
        \\    {
        \\        var owned: Buffer = .{};
        \\        defer owned.deinit(gpa);
        \\    }
        \\}
    );
}

test "ref-counted-copy-without-dupe: a retracted store does not prove live published ownership" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\const Sink = struct {
        \\    held: Buffer,
        \\    fn save(self: *Sink, value: Buffer) void {
        \\        self.held = value;
        \\        self.held = .{};
        \\    }
        \\    fn deinit(self: *Sink, gpa: std.mem.Allocator) void { self.held.deinit(gpa); }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer, sink: *Sink) !void {
        \\    var owned = source;
        \\    errdefer owned.deinit(gpa);
        \\    sink.save(owned);
        \\    try fail();
        \\}
    );
}

test "ref-counted-copy-without-dupe: metadata edits do not duplicate a returned owner" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\pub fn copy(source: Buffer) Buffer {
        \\    source.count = 1;
        \\    return source;
        \\}
    );
}

test "ref-counted-copy-without-dupe: exclusive catch cleanup does not overlap success consumption" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\fn reserve(fail: bool) !void { if (fail) return error.Failed; }
        \\fn consume(gpa: std.mem.Allocator, value: Buffer) void { gpa.free(value.bytes); }
        \\pub fn copy(gpa: std.mem.Allocator, source: Buffer, fail: bool) !void {
        \\    reserve(fail) catch |err| {
        \\        var refused = source;
        \\        refused.deinit(gpa);
        \\        return err;
        \\    };
        \\    consume(gpa, source);
        \\}
    );
}

test "ref-counted-copy-without-dupe: aggregate fields transfer without an implicit source destructor" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Inner = struct {
        \\    bytes: []u8,
        \\    fn deinit(self: Inner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\const Owner = struct {
        \\    inner: Inner,
        \\    fn deinit(self: Owner, gpa: std.mem.Allocator) void { self.inner.deinit(gpa); }
        \\};
        \\pub fn move(source: Owner) Owner { return .{ .inner = source.inner }; }
    );
}

test "ref-counted-copy-without-dupe: aggregate fields with two explicit cleanups still warn" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Inner = struct {
        \\    bytes: []u8,
        \\    fn deinit(self: Inner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\const Owner = struct {
        \\    inner: Inner,
        \\    fn deinit(self: Owner, gpa: std.mem.Allocator) void { self.inner.deinit(gpa); }
        \\};
        \\pub fn copy(gpa: std.mem.Allocator, source: Owner) Owner {
        \\    defer source.deinit(gpa);
        \\    return .{ .inner = source.inner };
        \\}
    );
}

test "ref-counted-copy-without-dupe: failed release preserves the sole owner for error cleanup" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: Owner, gpa: std.mem.Allocator, fail: bool) !void {
        \\        if (fail) return error.Refused;
        \\        gpa.free(self.bytes);
        \\    }
        \\};
        \\pub fn consume(gpa: std.mem.Allocator, source: Owner, fail: bool) !void {
        \\    var owned = source;
        \\    errdefer owned.release(gpa, false) catch {};
        \\    try owned.release(gpa, fail);
        \\}
    );
}

test "ref-counted-copy-without-dupe: release that consumes before failure still overlaps rollback" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: Owner, gpa: std.mem.Allocator, fail: bool) !void {
        \\        gpa.free(self.bytes);
        \\        if (fail) return error.Refused;
        \\    }
        \\};
        \\pub fn consume(gpa: std.mem.Allocator, source: Owner, fail: bool) !void {
        \\    var owned = source;
        \\    errdefer owned.release(gpa, false) catch {};
        \\    try owned.release(gpa, fail);
        \\}
    );
}

test "ref-counted-copy-without-dupe: a field-named capability method is not a field copy" {
    try testing.expectNoFireTyped(check,
        \\const Pool = struct {
        \\    used: usize,
        \\    fn release(self: *Pool, n: usize) void { self.used -= n; }
        \\};
        \\const Ledger = struct {
        \\    backing: *Pool,
        \\    fn pool(self: Ledger) *Pool { return self.backing; }
        \\};
        \\const Charge = struct {
        \\    pool: *Pool,
        \\    fn deinit(self: Charge) void { self.pool.release(1); }
        \\};
        \\pub fn build(source: Ledger) Charge { return .{ .pool = source.pool() }; }
    );
}

test "ref-counted-copy-without-dupe: discarded borrowed result creates no second cleanup obligation" {
    try testing.expectNoFireTyped(check, whole_handoff_owner ++
        \\fn get(self: *const Buffer) Buffer { return self.*; }
        \\pub fn consume(gpa: std.mem.Allocator, source: Buffer) void {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    _ = get(&owned);
        \\}
    );
}

test "ref-counted-copy-without-dupe: returned borrowed handle and source cleanup overlap" {
    try testing.expectFiresTyped(check, R, whole_handoff_owner ++
        \\fn get(self: *const Buffer) Buffer { return self.*; }
        \\pub fn duplicate(gpa: std.mem.Allocator, source: Buffer) Buffer {
        \\    var owned = source;
        \\    defer owned.deinit(gpa);
        \\    return get(&owned);
        \\}
    );
}

test "ref-counted-copy-without-dupe: canonical increment balances only the same owned resource" {
    const prelude =
        \\const Ref = struct {
        \\    count: usize,
        \\    metrics: usize,
        \\    fn retain(self: *Ref) void { self.count += 1; }
        \\    fn fake(self: *Ref) void { self.count |= 1; }
        \\    fn metricRetain(self: *Ref) void { self.metrics += 1; }
        \\    fn metricDrop(self: *Ref) void { self.metrics -= 1; }
        \\    fn mixed(self: *Ref) void { self.metrics += 1; self.count += 1; }
        \\    fn retainOther(_: *Ref, other: *Ref) void { other.count += 1; }
        \\    fn recycled(self: *Ref) void { self.count -= 1; self.count += 1; }
        \\    fn uncertain(self: *Ref, action: *const fn () void) void { self.count += 1; action(); }
        \\    fn wrapping(self: *Ref) void { self.count +%= 1; }
        \\    fn saturating(self: *Ref) void { self.count +|= 1; }
        \\    fn falseRetain(self: *Ref) void { if (false) self.count += 1; }
        \\    fn conditionalRetain(self: *Ref, flag: bool) void { if (flag) self.count += 1; }
        \\    fn alternate(self: *Ref, other: *Ref, flag: bool) *Ref {
        \\        if (flag) { self.count += 1; return self; }
        \\        return other;
        \\    }
        \\    fn balanced(self: *Ref, flag: bool) void {
        \\        if (flag) self.count += 1 else self.count += 1;
        \\    }
        \\    fn release(self: *Ref) void { self.count -= 1; }
        \\};
        \\const Handle = struct {
        \\    item: *Ref,
        \\    fn deinit(self: Handle) void { self.item.release(); }
        \\};
    ;
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn copy(source: Handle) Handle {
        \\    defer source.deinit();
        \\    const alias = source.item;
        \\    alias.retain();
        \\    return .{ .item = source.item };
        \\}
    );
    try testing.expectFiresTyped(check, R, prelude ++
        \\pub fn copy(source: Handle) Handle {
        \\    defer source.deinit();
        \\    source.item.fake();
        \\    return .{ .item = source.item };
        \\}
    );
    try testing.expectFiresTyped(check, R, prelude ++
        \\pub fn copy(source: Handle, other: Handle) Handle {
        \\    defer source.deinit();
        \\    other.item.retain();
        \\    return .{ .item = source.item };
        \\}
    );
    inline for (.{
        .{ "source: Handle", "source.item.falseRetain();" },
        .{ "source: Handle, flag: bool", "source.item.conditionalRetain(flag);" },
        .{ "source: Handle", "source.item.recycled();" },
        .{ "source: Handle, action: *const fn () void", "source.item.uncertain(action);" },
        .{ "source: Handle", "source.item.wrapping();" },
        .{ "source: Handle", "source.item.saturating();" },
        .{ "source: Handle, other: Handle, flag: bool", "_ = source.item.alternate(other.item, flag);" },
        .{ "source: Handle", "source.item.metricRetain();" },
    }) |case| {
        try testing.expectFiresTyped(check, R, prelude ++
            "pub fn copy(" ++ case[0] ++ ") Handle {\n" ++
            "    defer source.deinit();\n" ++
            "    " ++ case[1] ++ "\n" ++
            "    return .{ .item = source.item };\n" ++
            "}\n"
        );
    }
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn copy(source: Handle, flag: bool) Handle {
        \\    defer source.deinit();
        \\    source.item.balanced(flag);
        \\    return .{ .item = source.item };
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn copy(source: Handle) Handle {
        \\    defer source.deinit();
        \\    source.item.mixed();
        \\    return .{ .item = source.item };
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn copy(source: Handle, other: Handle) Handle {
        \\    defer source.deinit();
        \\    other.item.retainOther(source.item);
        \\    return .{ .item = source.item };
        \\}
    );
    try testing.expectFiresTyped(check, R, prelude ++
        \\pub fn copy(source: Handle, other: Handle) Handle {
        \\    defer source.deinit();
        \\    source.item.retainOther(other.item);
        \\    return .{ .item = source.item };
        \\}
    );
}

test "ref-counted-copy-without-dupe: retaining an old field alias does not acquire its replacement" {
    try testing.expectFiresTyped(check, R,
        \\const Ref = struct {
        \\    count: usize,
        \\    fn retain(self: *Ref) void { self.count += 1; }
        \\    fn release(self: *Ref) void { self.count -= 1; }
        \\};
        \\const Handle = struct {
        \\    item: *Ref,
        \\    fn deinit(self: Handle) void { self.item.release(); }
        \\};
        \\pub fn copy(input: Handle, other: *Ref) Handle {
        \\    var source = input;
        \\    defer source.deinit();
        \\    const old = source.item;
        \\    source.item = other;
        \\    old.retain();
        \\    return .{ .item = source.item };
        \\}
    );
}
