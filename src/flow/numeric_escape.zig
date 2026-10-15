//! The pointer-escape and reachability model of the numeric oracle.
//!
//! One question, asked from many places: when this walk reaches a call, a
//! store or a builtin, can that effect write the storage a fact is about?
//! Answering it needs three things, and they are all here:
//!
//!   * which names this body takes the ADDRESS of, and which local bindings
//!     hold a POINTER (`collectEscapeRoots`, once per body);
//!   * what such a pointer NAMES at each point of the body, read through the
//!     chain of bindings in force at that point (`resolveAliasChain`);
//!   * whether one call hands the callee storage overlapping a path
//!     (`pathEscapedBy`, and the field-level receiver proof that keeps an
//!     immutable predicate from reading like a mutation).
//!
//! The oracle's `State` and `Oracle` live in `value_range.zig` and are used
//! here as the ONE representation of a walk — this module adds no second
//! state, no callback table and no interface layer.  What it owns is the
//! reasoning about storage, which is a different reason for the code to
//! change than the statement walk, the numeric evaluator or the loop prover.
//!
//! A failed resolver query is not a missing proof. Nonthrowing reachability
//! helpers retain the first error in `Oracle.summary_error`; the enclosing
//! throwing walk returns it before publishing an answer.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");
const file_cache_mod = @import("../cache/file_cache.zig");
const numeric_nodes = @import("../model/numeric_nodes.zig");
const value_range = @import("value_range.zig");

const Oracle = value_range.Oracle;
const State = value_range.State;

/// A `const P = &path` binding: handing `P` to a callee hands it the storage
/// behind `path`, so `f(P)` must invalidate exactly what `f(&path)` does.
/// `token` is the first token of the binding statement, so the target in
/// force at a use is the LAST binding before that use — a later `P = &other`
/// supersedes the declaration. Unless `fresh` establishes new storage, an
/// empty `path` marks an unresolved target that may name any storage.
pub const EscapeAlias = struct {
    local: []const u8,
    path: []const u8,
    token: Ast.TokenIndex,
    /// A successful standard allocator creation names new storage, not a
    /// pre-existing object. The binding token is its allocation identity.
    fresh: bool = false,
};

/// The storage a pointer chain names, as the leading storage plus the
/// projections applied to it on the way there.  Every part is BORROWED from
/// the source spelling that recorded it; nothing here is allocated.
const AliasStorage = struct {
    /// The storage the chain ends at, spelled on its own.
    lead: []const u8 = "",
    /// The `.field` / `[i]` pieces each hop projected off the way, in the order
    /// they APPLY to `lead`.  The answer is `lead` with these appended in that
    /// order, and `orderApplied` is what puts them in it.
    suffixes: []const []const u8 = &.{},
    /// The chain ended at a binding this body RECORDED and could not resolve,
    /// or it did not end at all.  A name with no binding at all is NOT this
    /// case: see `unbound`.
    unresolved: bool = true,
    /// The chain ended at a name this body never bound.  Parameters are never
    /// bound by the body that receives them, so this is what a pointer
    /// parameter looks like, and it is answered by a set rather than by an
    /// assumption — see `resolveAliasChain`.
    unbound: bool = false,
    /// The allocation binding reached by the chain, including pointer copies.
    fresh_token: ?Ast.TokenIndex = null,
};

/// How many pointer bindings one alias chain may have before the walk gives
/// up.  A chain longer than this, or one that comes back to a name it has
/// already visited, is answered as unresolved rather than approximated.
const alias_hop_cap: usize = 8;

/// How many calls and direct writes one expression's scan will record before
/// it gives up and reports the effects as reaching everything.  An expression
/// this long is not a shape the step budget is sized for either, so widening
/// the scan would only move the cost somewhere less visible.
const effect_scan_cap = 64;

/// Everything one expression can do, gathered once so a whole fact set can be
/// filtered without re-walking the same subtree once per name.
pub const EffectScan = struct {
    calls: [effect_scan_cap]Ast.Node.Index = undefined,
    call_count: usize = 0,
    writes: [effect_scan_cap][]const u8 = undefined,
    write_count: usize = 0,
    write_pointers: [effect_scan_cap]?Ast.Node.Index = @splat(null),
    /// False once the subtree held an effect this scan does not model.  The
    /// answer is then "reaches everything", which is the sound direction: a
    /// missing effect would keep a fact that is no longer true.
    complete: bool = true,

    pub fn reaches(scan: *const EffectScan, o: *Oracle, path: []const u8) bool {
        if (!scan.complete) return true;
        for (scan.writes[0..scan.write_count], scan.write_pointers[0..scan.write_count]) |write, pointer| {
            if (pointer) |operand| {
                if (escapeReaches(o, operand, path)) return true;
            } else if (writeReachesPath(write, path)) return true;
        }
        for (scan.calls[0..scan.call_count]) |call| {
            if (pathEscapedBy(o, call, path)) return true;
        }
        return false;
    }
};

/// One body-wide reading for the facts a per-call query needs: roots whose
/// address is taken (`&x`) AND handed to somebody, locals whose own value is
/// a pointer, and what each such pointer names at each point of the body.  A
/// path rooted at a pointer — `h.data` for `h: *Holder` — is reachable
/// through every callee the pointer is handed to, so it is not call-stable.
///
/// The LEXICAL half of that — which `&x` are taken, which statements write a
/// name, and WHEN — is a property of the body and comes from the file cache's
/// ONE lazily built per-body index, so a body pays for it once for the whole
/// analysis rather than once per walk and again for every interprocedural
/// child oracle.  The RESOLVED half is a property of this walk: which names
/// are pointer roots depends on the type engine, and what a chain resolves to
/// depends on every binding in force before that token, so it is replayed
/// here in source order against this walk's own state.
///
/// Replaying one ordered list is the same result the two separate passes gave.
/// A declaration that could MAKE a name a pointer sits at its own node, and
/// a plain assignment to a name can only follow the declaration that binds
/// it, so by the time a write is read the root set already holds exactly the
/// entries the earlier pass would have finished adding — while the TARGETS,
/// which each depend on the bindings recorded before them, keep the order the
/// source wrote them in.
pub fn collectEscapeRoots(o: *Oracle) error{OutOfMemory}!void {
    const index = try bodyEscapeIndex(o);
    for (index.addressed) |root| try o.addressed.add(o.gpa, root);
    for (index.writes) |write| {
        if (write.declares) try markPointerLocal(o, write.name, write.type_node, write.init);
        if (!o.pointer_roots.contains(write.name)) continue;
        try recordPointerTarget(o, write.name, write.token, write.init, write.unconditional);
    }
}

/// This body's escape index.
///
/// BORROWED from the file cache when the query has one: the cache builds it
/// once per fn body and owns it for the snapshot's lifetime, so every walk of
/// that body — the query's own and every child oracle it spawns — reads one
/// table instead of re-walking the file's node array.
///
/// OWNED here only on the cache-less path, where there is no per-file owner to
/// borrow from: several unit tests and the `.ptr[0..N]` rule pass no cache at
/// all.  That copy is released by `Oracle.deinit` with the rest of what the
/// oracle owns, so the two lifetimes never overlap in one value.
///
/// The failure convention is the one `requiredNodes` already established for
/// this module's other per-file index, and the reason is the same: this
/// function CACHES what it derives, so an index that only failed to build
/// would otherwise cache "this body has no escape roots" — a fact the walk
/// cannot support.  So the cache-less build propagates, and the cached one
/// returns the cache's own error, which becomes `error.OutOfMemory` at the
/// query entry instead of an answer.
fn bodyEscapeIndex(o: *Oracle) error{OutOfMemory}!*const file_cache_mod.FileCache.EscapeRootIndex {
    if (o.body_index) |borrowed| return borrowed;
    if (o.cache) |cache| {
        const built = try cache.escapeRoots(o.body);
        o.body_index = built;
        return built;
    }
    const tree = o.tree;
    const first = tree.firstToken(o.body);
    const last = tree.lastToken(o.body);
    var addressed: std.ArrayListUnmanaged([]const u8) = .empty;
    errdefer addressed.deinit(o.gpa);
    var writes: std.ArrayListUnmanaged(file_cache_mod.FileCache.EscapeWrite) = .empty;
    errdefer writes.deinit(o.gpa);
    var statement_buf: [2]Ast.Node.Index = undefined;
    const statements = bodyStatements(tree, o.body, &statement_buf);
    var cursor: usize = 0;
    // Sparse, so there is nothing to pre-size: the list grows to what the body
    // actually holds of these tags, and a sized list would reserve for nodes it
    // never keeps.  The whole file's node array is read here because there is
    // no cache to have built the filtered table already.
    for (tree.nodes.items(.tag), 0..) |tag, raw_node| {
        const node: Ast.Node.Index = @enumFromInt(raw_node);
        if (!numeric_nodes.isIndexedTag(tag)) continue;
        const node_first = tree.firstToken(node);
        if (node_first < first or tree.lastToken(node) > last) continue;
        while (cursor < statements.len and @intFromEnum(statements[cursor]) < @intFromEnum(node)) cursor += 1;
        const unconditional = cursor < statements.len and statements[cursor] == node;
        switch (tag) {
            .address_of => {
                if (addressIsDiscarded(tree, node)) continue;
                const root = tokens.rootIdentifier(tree, tree.nodeData(node).node) orelse continue;
                try addressed.append(o.gpa, tree.tokenSlice(tree.nodeMainToken(root)));
            },
            .simple_var_decl, .local_var_decl, .aligned_var_decl => {
                const decl = tree.fullVarDecl(node) orelse continue;
                try writes.append(o.gpa, .{
                    .name = tree.tokenSlice(decl.ast.mut_token + 1),
                    .type_node = decl.ast.type_node.unwrap(),
                    // `var x: T;` declares without writing a value, and the
                    // record still has to stand for the DECLARATION: it is what
                    // marks a `*T`-declared local a pointer root, and dropping
                    // it would lose that marking.  The declaration
                    // node itself stands in for the value it has none — the
                    // type engine answers a `var_decl` node with that
                    // declaration's own type, so the marked/not-marked
                    // reading is the declared one, and the alias recorded
                    // from it stays unresolved (`""`), which is the top of
                    // this module's lattice.
                    .init = decl.ast.init_node.unwrap() orelse node,
                    .token = node_first,
                    .unconditional = unconditional,
                    .declares = true,
                });
            },
            .assign => {
                const data = tree.nodeData(node).node_and_node;
                if (tree.nodeTag(data[0]) != .identifier) continue;
                try writes.append(o.gpa, .{
                    .name = tree.tokenSlice(tree.nodeMainToken(data[0])),
                    .type_node = null,
                    .init = data[1],
                    .token = node_first,
                    .unconditional = unconditional,
                    .declares = false,
                });
            },
            else => {},
        }
    }
    var addressed_owned: ?[]const []const u8 = null;
    errdefer if (addressed_owned) |slice| o.gpa.free(slice);
    addressed_owned = try addressed.toOwnedSlice(o.gpa);
    var writes_owned: ?[]const file_cache_mod.FileCache.EscapeWrite = null;
    errdefer if (writes_owned) |slice| o.gpa.free(slice);
    writes_owned = try writes.toOwnedSlice(o.gpa);
    // Ownership moves to the oracle on the last two lines.  The `errdefer`s
    // above now own both buffers — `toOwnedSlice` emptied the lists before it
    // returned — so a failure past this point frees exactly what was handed
    // over, and a success leaves the lists with nothing to free.
    o.body_index_owned = .{ .addressed = addressed_owned.?, .writes = writes_owned.? };
    o.body_index = &o.body_index_owned.?;
    return o.body_index.?;
}

/// The statements of one block node, in source order.  `buf` backs the
/// one- and two-statement shapes, which the node table stores inline.
fn bodyStatements(
    tree: *const Ast,
    block_node: Ast.Node.Index,
    buf: *[2]Ast.Node.Index,
) []const Ast.Node.Index {
    return switch (tree.nodeTag(block_node)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(block_node).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const data = tree.nodeData(block_node);
            buf[0] = data.opt_node_and_opt_node[0].unwrap() orelse break :blk &.{};
            if (data.opt_node_and_opt_node[1].unwrap()) |second| {
                buf[1] = second;
                break :blk buf[0..2];
            }
            break :blk buf[0..1];
        },
        else => &.{},
    };
}

/// Recognize a direct `_ = &x` at a statement boundary. Other contexts
/// remain escaped; the prefix excludes struct fields and field assignments.
fn addressIsDiscarded(tree: *const Ast, node: Ast.Node.Index) bool {
    const amp = tree.firstToken(node);
    if (amp < 3 or tree.tokenTag(amp - 1) != .equal) return false;
    if (tree.tokenTag(amp - 2) != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(amp - 2), "_")) return false;
    return switch (tree.tokenTag(amp - 3)) {
        .semicolon, .l_brace, .r_brace => true,
        else => false,
    };
}

/// Does the type node SPELL a pointer — `*T`, `?*T`, `[*]T`?
///
/// This reads syntax only, which is what makes it usable before a type engine
/// is consulted and on the token-only path where none is attached at all.  A
/// type that is pointer-valued without saying so (`const P = *T;`) is the
/// engine's question, asked separately; this one answers for the declaration
/// that writes a pointer type out.
///
/// Pointer AST tags also represent slices. Read the full pointer shape so all
/// pointer spellings are covered without treating a by-value slice header as
/// storage reached through an address.
pub fn spellingIsPointer(tree: *const Ast, node: Ast.Node.Index) bool {
    const pointer_node = if (tree.nodeTag(node) == .optional_type)
        tree.nodeData(node).node
    else
        node;
    const pointer = tree.fullPtrType(pointer_node) orelse return false;
    return pointer.size != .slice;
}

/// Record `name` as pointer-valued when its declaration proves it: an explicit
/// `*T` / `?*T` / `[*]T` type, a `&path` initializer, or a type the engine
/// resolves to a pointer/optional.  An unresolved initializer is NOT treated
/// as a pointer — a `const x = <call>` binding is a by-value header far more
/// often than not, and reading it as a pointer would discard every fact about
/// a struct returned from a helper.
///
/// A pointer-typed local joins `indirection_roots` as well, because its own
/// fields are reached THROUGH that address.  A slice-typed local does not: its
/// header is a by-value register-sized value in this frame, so `local.len` is
/// a load from the local's own storage that a callee cannot rewrite (see
/// `callStableRoot`).
fn markPointerLocal(
    o: *Oracle,
    name: []const u8,
    type_node: ?Ast.Node.Index,
    init: ?Ast.Node.Index,
) error{OutOfMemory}!void {
    const tree = o.tree;
    if (type_node) |declared| {
        if (spellingIsPointer(tree, declared)) {
            try o.pointer_roots.add(o.gpa, name);
            try o.indirection_roots.add(o.gpa, name);
            return;
        }
    }
    const target = if (init) |node| value_range.unwrapGrouped(tree, node) else return;
    if (tree.nodeTag(target) == .address_of) {
        try o.pointer_roots.add(o.gpa, name);
        try o.indirection_roots.add(o.gpa, name);
        return;
    }
    // A COPY of a pointer is a pointer: `const alias = state` names the same
    // address under a second name, so a write through `alias` is a write
    // through `state`.  The initializer's pointer-ness is established, never
    // guessed — by a name this body has already marked, or by the parameter
    // annotation in the proto.  The proto is read directly because the escape
    // roots are collected before the parameters are seeded.
    if (tree.nodeTag(target) == .identifier) {
        const spelled = tree.tokenSlice(tree.nodeMainToken(target));
        if (o.pointer_roots.contains(spelled) or parameterIsPointer(o, spelled)) {
            try o.pointer_roots.add(o.gpa, name);
            try o.indirection_roots.add(o.gpa, name);
            return;
        }
    }
    if (o.cache) |cache| {
        // An explicit slice type coerces a string or array-pointer initializer
        // into a by-value header. Classify the binding, not that initializer.
        const value_type = type_node orelse target;
        if (cache.typeRefIsPointerLike(value_type) != true) return;
        try o.pointer_roots.add(o.gpa, name);
        if (valueIsAddress(o, value_type)) try o.indirection_roots.add(o.gpa, name);
    }
}

/// Is `name` a parameter of the analyzed function declared with a pointer
/// type?  Read from the function's own proto rather than from
/// `pointer_roots`, which is still empty of parameters at the point the escape
/// roots are collected.
fn parameterIsPointer(o: *Oracle, name: []const u8) bool {
    const tree = o.tree;
    const declaration = value_range.enclosingFnDecl(o) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    var parameters = proto.iterate(tree);
    while (parameters.next()) |parameter| {
        const name_token = parameter.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), name)) continue;
        const type_node = parameter.type_expr orelse return false;
        return spellingIsPointer(tree, type_node);
    }
    return false;
}

/// Does a value of `node`'s type live outside the binding's own frame slot?
/// Resolved through the type engine, so an alias (`const P = *T;`) and an
/// inferred binding are both classified by their actual type, never by the
/// spelling of the call that produced them. Null from a successful query (no
/// type engine, unresolved) is a "no": the caller has already established the
/// value is pointer-LIKE, and the by-value reading is the one a slice header
/// needs. A failed query must not establish that reading: it can retain a
/// field fact across a call that writes through the address.
pub fn valueIsAddress(o: *Oracle, node: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const raw_pointer = resolver.isRawSinglePointerType(node) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    };
    if (raw_pointer == true) return true;
    const optional_pointer = resolver.optionalPayloadIsPointer(node) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    };
    return optional_pointer == true;
}

/// Record what `name` names from `token` on. Only the toolchain allocator's
/// `create` contract establishes fresh storage; other call results and
/// conditional rebindings remain unresolved.
fn recordPointerTarget(
    o: *Oracle,
    name: []const u8,
    token: Ast.TokenIndex,
    init: ?Ast.Node.Index,
    unconditional: bool,
) error{OutOfMemory}!void {
    const tree = o.tree;
    var path: []const u8 = "";
    var fresh = false;
    if (unconditional) {
        if (init) |node| {
            const target = value_range.unwrapGrouped(tree, node);
            fresh = stdAllocatorCreatesStorage(o, target);
            switch (tree.nodeTag(target)) {
                .address_of => path = value_range.nodeSrc(tree, value_range.unwrapGrouped(tree, tree.nodeData(target).node)),
                .identifier => {
                    const spelled = tree.tokenSlice(tree.nodeMainToken(target));
                    // A pointer bound to another pointer names what THAT one
                    // names, and the answer stands even when the chain is not
                    // resolvable past that: `const alias = state` is a fact
                    // about `alias` even when `state` is a parameter whose
                    // target lives in the caller's frame.  Following the
                    // chain instead would report "unresolved" and lose the
                    // one thing the binding does establish — that the two
                    // names are the same address.
                    if (o.pointer_roots.contains(spelled) or parameterIsPointer(o, spelled)) {
                        path = spelled;
                    } else path = try resolveEscapePath(o, spelled, token);
                },
                else => {},
            }
        }
    }
    try o.escape_aliases.append(o.gpa, .{ .local = name, .path = path, .token = token, .fresh = fresh });
}

fn stdAllocatorCreatesStorage(o: *Oracle, initializer: Ast.Node.Index) bool {
    const tree = o.tree;
    const node = value_range.unwrapGrouped(tree, if (tree.nodeTag(initializer) == .@"try") tree.nodeData(initializer).node else initializer);
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    if (call.ast.params.len != 1) return false;
    const resolver = (o.cache orelse return false).zls orelse return false;
    const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) {
        .function => |reference| reference,
        .unknown, .not_callable => return false,
    };
    if (!std.mem.eql(u8, reference.tree.tokenSlice(reference.fn_token + 1), "create")) return false;
    return resolver.declaredInToolchainFile(reference.handle, "/std/mem/Allocator.zig") catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    };
}

/// The storage the pointer `name` names at `at`, following the chain of
/// pointer bindings.  The reachable set is the UNION over every binding that
/// can be in force there: a binding that ran on this path and an earlier one
/// that a skipped branch may have replaced both count, so a pointer rebound
/// inside a branch or a loop resolves to nothing specific.  An empty `path`
/// is therefore the top of that lattice — "not established in this body" —
/// and a call reaching such a pointer may write anything.
///
/// The returned slice is MINTED, because an `EscapeAlias` stores it and has to
/// outlive the walk that resolved it.  The mint is memoised on the oracle, so
/// a given chain spelling is composed once per query rather than once per use,
/// and `resolveAliasChain` itself allocates nothing.
pub fn resolveEscapePath(o: *Oracle, name: []const u8, at: Ast.TokenIndex) error{OutOfMemory}![]const u8 {
    if (!o.pointer_roots.contains(name)) return "";
    var suffixes: [alias_hop_cap][]const u8 = undefined;
    const chain = resolveAliasChain(o, name, at, &suffixes);
    return mintAliasPath(o, chain);
}

/// The binding of `local` in force at `at`, with the token that captured it.
///
/// The TOKEN is what makes a chain walk correct.  It says WHEN this pointer
/// took the value it holds, and the next hop has to be read as of that moment
/// rather than as of wherever the chain happens to be walked to — which is the
/// whole difference between following an alias and following its current value.
fn latestEscapeBinding(o: *const Oracle, local: []const u8, at: Ast.TokenIndex) ?EscapeAlias {
    var latest: ?EscapeAlias = null;
    for (o.escape_aliases.items) |entry| {
        if (!std.mem.eql(u8, entry.local, local)) continue;
        if (entry.token >= at) continue;
        if (latest == null or entry.token > latest.?.token) latest = entry;
    }
    return latest;
}

/// Follow the pointer chain rooted at `name` to the storage it names at `at`.
///
/// Each hop is read as of the token that CAPTURED it, never as of `at` itself,
/// so a name rebound after an alias took its value still resolves through the
/// value the alias captured.
///
/// A hop whose recorded spelling is rooted at a POINTER ROOT is a projection,
/// not an endpoint: `const b = &a.count` records `a.count`, `a` is the pointer,
/// and the chain has to continue at `a` and apply `.count` to whatever `a`
/// turns out to name.  Terminating on the spelling `a.count` would hand the
/// caller a pointer's name where storage was asked for, and nothing the write
/// reaches would be invalidated — the defect this split exists to prevent.
///
/// Two dead-ends are kept apart, and the difference is what has to be dropped:
///
///   * a binding this body RECORDED whose target it could not resolve — the
///     empty path `recordPointerTarget` writes for a conditional rebinding —
///     leaves the answer `.unresolved`, because the pointer names storage
///     nothing here can name;
///   * NO binding at all is what a pointer PARAMETER looks like.  A parameter
///     was aimed before this frame existed, so it cannot name a fresh local of
///     this body — but it can name ANOTHER PARAMETER's storage, because two
///     parameters may be handed the same object, and it can name any local
///     whose address this body handed out.  Answering with its own spelling
///     alone would retire `state.index` and leave `other.index` standing for
///     `alias = state; alias.index = 0`, which is a false negative whenever
///     the two are the same object.  The caller therefore drops the whole set
///     that could be behind it — every pointer root and every name whose
///     address escaped — and keeps the rest, which is the part the frame
///     lifetime rules out.
///
/// It is marked `.unbound` rather than answered here because the set is a
/// property of the STATE, not of this chain.
fn resolveAliasChain(
    o: *Oracle,
    name: []const u8,
    at: Ast.TokenIndex,
    suffixes: *[alias_hop_cap][]const u8,
) AliasStorage {
    if (!o.pointer_roots.contains(name)) return .{};
    var local = name;
    var anchor = at;
    var count: usize = 0;
    var hops: usize = 0;
    while (hops < alias_hop_cap) : (hops += 1) {
        const entry = latestEscapeBinding(o, local, anchor) orelse return .{
            .lead = local,
            .suffixes = orderApplied(suffixes[0..count]),
            .unresolved = false,
            .unbound = true,
        };
        if (entry.fresh) return .{
            .lead = local,
            .suffixes = orderApplied(suffixes[0..count]),
            .unresolved = false,
            .fresh_token = entry.token,
        };
        const bound = entry.path;
        if (bound.len == 0) return .{};
        const lead = rootText(bound);
        const suffix = bound[lead.len..];
        if (suffix.len != 0) {
            if (count == suffixes.len) return .{};
            suffixes[count] = suffix;
            count += 1;
        }
        // The chain ENDS at the root, never at the whole spelling.  `bound`
        // still carries the projection this hop added, and that projection is
        // already in `suffixes` — handing `bound` back as the lead would apply
        // it twice, so `const a = &holder; const b = &a.count` would answer
        // `holder.count.count`.
        if (!o.indirection_roots.contains(lead)) {
            return .{
                .lead = lead,
                .suffixes = orderApplied(suffixes[0..count]),
                .unresolved = false,
            };
        }
        local = lead;
        anchor = entry.token;
    }
    return .{};
}

/// True only when this binding chain ends at a certified fresh allocation.
pub fn hasFreshStorage(o: *Oracle, name: []const u8, at: Ast.TokenIndex) bool {
    var suffixes: [alias_hop_cap][]const u8 = undefined;
    return resolveAliasChain(o, rootText(name), at, &suffixes).fresh_token != null;
}

/// The collected projections in the order they APPLY to the storage the chain
/// ends at, which is the reverse of the order the hops met them.
///
/// A hop's projection is applied to whatever every LATER hop resolves, so the
/// outermost hop's piece goes on last.  `const a = &holder; const b = &a.inner;
/// const c = &b.count` pushes `.count` then `.inner` and applies `.inner` then
/// `.count`, giving `holder.inner.count` — in push order it would be
/// `holder.count.inner`, which is a different object.
///
/// The reversal is done HERE, once, on the buffer the caller owns.  Every
/// consumer then appends `suffixes` in order, so there is one composition
/// rather than three that have to agree about which way round it goes.
fn orderApplied(suffixes: [][]const u8) [][]const u8 {
    var left: usize = 0;
    var right = if (suffixes.len == 0) 0 else suffixes.len - 1;
    while (left < right) : (left += 1) {
        right -= 1;
        const held = suffixes[left];
        suffixes[left] = suffixes[right];
        suffixes[right] = held;
    }
    return suffixes;
}

/// The chain's spelling as one string, written into `buffer` when it fits.
/// Null when there is none to write, and every caller answers that
/// conservatively rather than truncating: a chain this long has no spelling to
/// compare, so the answer becomes the one that assumes it reaches everything.
///
/// An UNBOUND chain is declined too, and deliberately.  Its lead is a
/// parameter's own name, but two parameters may be handed the same object, so
/// that name is not the whole of what a write or a call behind it can reach —
/// spelling it alone would be a narrowing.  `aliasedTarget` answers that case
/// with a set instead, and `escapeReaches` falls through to the rule it
/// already had for an unresolved parameter pointer.
fn composeAliasPath(chain: AliasStorage, buffer: []u8) ?[]const u8 {
    if (chain.unresolved or chain.unbound) return null;
    if (chain.lead.len == 0 or chain.lead.len > buffer.len) return null;
    @memcpy(buffer[0..chain.lead.len], chain.lead);
    var written = chain.lead.len;
    for (chain.suffixes) |suffix| {
        if (written + suffix.len > buffer.len) return null;
        @memcpy(buffer[written .. written + suffix.len], suffix);
        written += suffix.len;
    }
    return buffer[0..written];
}

/// The chain's spelling as a slice that OUTLIVES this call, for the two
/// callers that store it: an `EscapeAlias` records it, and a fact keyed on it
/// has to survive the walk.  It composes in exactly the order
/// `composeAliasPath` does — `resolveAliasChain` has already put `suffixes` in
/// application order, so there is one composition rather than three that have
/// to agree about which way round it goes.
///
/// The mint is memoised on the oracle, so a chain spelling this walk has
/// already produced costs a lookup and not an allocation, and it allocates at
/// most once per distinct spelling per query.
fn mintAliasPath(o: *Oracle, chain: AliasStorage) error{OutOfMemory}![]const u8 {
    if (chain.unresolved) return "";
    if (chain.lead.len == 0) return "";
    var storage = chain.lead;
    for (chain.suffixes) |suffix| storage = try value_range.internPath(o, storage, suffix);
    return storage;
}

/// Is this pointer root a parameter of the analyzed function rather than one
/// of its locals?  Only a local can hold a pointer this body established, so
/// the two need different treatment when its target is unknown.
fn isParameterRoot(o: *const Oracle, name: []const u8) bool {
    for (o.locals) |binding| {
        if (!std.mem.eql(u8, binding.name, name)) continue;
        return binding.origin == .param;
    }
    return false;
}

/// Is `name` a bare local this body binds?
///
/// No `addressed` veto here, deliberately.  `addressed` is a whole-body fact —
/// "this body's source takes the address of `x` SOMEWHERE" — and reading it as
/// a per-call test meant one `&x` anywhere in the body destroyed every fact
/// about `x` at every call in it, including a call handed the address of a
/// completely different name.  Whether THIS effect can write `x` is
/// `effect.reaches`, which answers false for an effect that provably cannot
/// and `true` for one it cannot read, so the conservative direction is kept
/// where it belongs instead of being spent in advance.
fn localScalarSurvivesCall(o: *const Oracle, name: []const u8) bool {
    if (std.mem.indexOfScalar(u8, name, '.') != null) return false;
    for (o.locals) |binding| if (std.mem.eql(u8, binding.name, name)) return true;
    return false;
}

/// A container path keeps its recorded length across a call when the root is a
/// by-value local whose address never escapes: the callee receives a copy of
/// the slice header, so nothing it does can resize the local.
///
/// `indirection_roots` is the exclusion list, and being on it is exactly the
/// reason a root is NOT call-stable: a root there holds an ADDRESS, so
/// `root.field` / `root.len` is a load through storage the callee may hold a
/// pointer to.  A slice-typed root is absent from it on purpose — its header
/// (`len`, `ptr`) is part of the local's own frame slot and no callee can
/// write that slot without the address having escaped, which `addressed`
/// already disqualifies.  `pointer_roots` still holds it for the escape model
/// (`pathEscapedBy`), so a call that is actually handed the slice still drops
/// the fact.
fn callStableRoot(o: *const Oracle, root: []const u8) bool {
    if (root.len == 0) return false;
    if (std.mem.indexOfScalar(u8, root, '.') != null) return false;
    if (o.addressed.contains(root) or o.indirection_roots.contains(root)) return false;
    return value_range.isLocalName(o, root);
}

/// A slice parameter's length belongs to this frame's copied header. Passing
/// the slice can expose its elements, but cannot expose this header unless
/// this body takes its address. Unknown types and shadowed names prove nothing.
fn copiedSliceLength(o: *Oracle, path: []const u8) bool {
    const root = rootText(path);
    if (!std.mem.eql(u8, path[root.len..], ".len") or !callStableRoot(o, root)) return false;
    const tree = o.tree;
    const declaration = value_range.enclosingFnDecl(o) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    var parameters = proto.iterate(tree);
    while (parameters.next()) |parameter| {
        const name_token = parameter.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), root)) continue;
        const type_node = parameter.type_expr orelse return false;
        const pointer = tree.fullPtrType(type_node) orelse return false;
        if (pointer.size != .slice) return false;
        for (o.locals) |binding| {
            if (binding.origin != .param and std.mem.eql(u8, binding.name, root)) return false;
        }
        return true;
    }
    return false;
}

/// A scalar fact survives a call when the callee cannot reach the storage the
/// fact is about: its receiver and its arguments name no overlapping storage.
///
/// The same rule answers for a bare local and for a field path
/// (`self.active_frames`), and the only difference is the root: a bare local is
/// one this body binds, and a field path is one whose ROOT this body binds.  A
/// fact on the root itself is asked about its own path, not about the root, so
/// a callee handed `holder` still keeps `holder.index` only if it names that
/// field — which is the point.
pub fn scalarSurvivesCall(o: *Oracle, name: []const u8, effect: value_range.Reach) bool {
    if (copiedSliceLength(o, name)) return true;
    if (std.mem.indexOfScalar(u8, name, '.') == null) {
        if (!localScalarSurvivesCall(o, name)) return false;
        // Ordinary calls receive this frame's scalar by value. Even an
        // anonymous temporary address in another argument cannot name it.
        // Do not apply this to subtree effects: they can assign the local.
        if (!o.addressed.contains(name)) switch (effect) {
            .one => |node| {
                var buffer: [1]Ast.Node.Index = undefined;
                if (o.tree.fullCall(&buffer, node) != null) return true;
            },
            .unknown, .subtree => {},
        };
        return !effect.reaches(o, name);
    }
    if (!value_range.isLocalName(o, rootText(name))) return false;
    return !effect.reaches(o, name);
}

pub fn containerSurvivesCall(o: *Oracle, path: []const u8, effect: value_range.Reach) bool {
    if (!value_range.isLocalName(o, rootText(path))) return false;
    return !effect.reaches(o, path);
}

/// Does the storage `path` names survive this effect?
///
/// This is the bare reach question the two functions above also ask, without
/// either of the shape tests they make alongside it.  A fact keyed on a FIELD
/// path is about storage the effect either reaches or does not, and no
/// spelling rule decides that: `self.bits` is not a container and not a local
/// scalar, and both of the tests above answer it `false` for that reason
/// alone, which would drop a proof an effect this far away never touched.
/// Anything the reach model cannot enumerate still answers `false` here, so
/// this widens what is KEPT and never what is dropped.
pub fn pathSurvivesCall(o: *Oracle, path: []const u8, effect: value_range.Reach) bool {
    if (path.len == 0) return false;
    return !effect.reaches(o, path);
}

pub fn productFactorSurvives(o: *Oracle, factor: value_range.ProductFactor, effect: value_range.Reach) bool {
    if (factor.is_container) return containerSurvivesCall(o, factor.key, effect);
    return scalarSurvivesCall(o, factor.key, effect);
}

/// A resolved leaf method can write one struct field without touching another.
/// Aliases, indirect writes, nested calls, unions and unknown types prove nothing.
fn methodKeepsField(o: *Oracle, call_node: Ast.Node.Index, receiver: Ast.Node.Index, path: []const u8) bool {
    const tree = o.tree;
    if (tree.nodeTag(receiver) != .identifier) return false;
    const receiver_name = tree.tokenSlice(tree.nodeMainToken(receiver));
    if (!std.mem.startsWith(u8, path, receiver_name) or path.len <= receiver_name.len + 1) return false;
    if (path[receiver_name.len] != '.') return false;
    const field = path[receiver_name.len + 1 ..];
    if (std.mem.indexOfScalar(u8, field, '.') != null) return false;
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    var call_buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, call_node) orelse return false;
    const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) {
        .function => |reference| reference,
        .unknown, .not_callable => return false,
    };
    if (reference.tree != tree) return false;
    const declaration = tokens.enclosingFnDecl(tree, reference.fn_token) orelse return false;
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, declaration) orelse return false;
    // The declaration is the identity, not the enclosing `fn_decl` node and
    // not the name: two containers in one file may each declare a `reset`, and
    // a receiver contract read off the wrong one is a claim about a body the
    // call never entered.  `enclosingFnDecl` already returns the function that
    // owns the resolved `fn` token; this asserts it, so every callee
    // resolution in this file answers the same question the same way.
    if (proto.ast.fn_token != reference.fn_token) return false;
    var parameters = proto.iterate(tree);
    const parameter = parameters.next() orelse return false;
    const name = tree.tokenSlice(parameter.name_token orelse return false);
    const type_node = parameter.type_expr orelse return false;
    if (!spellingIsPointer(tree, type_node)) return false;
    const type_name = tokens.typeNameFromTokens(tree, tree.firstToken(type_node), tree.lastToken(type_node)) orelse return false;
    const owner = cache.resolvedTypeAcrossImports(type_name) orelse return false;
    if (owner.info.kind != .struct_) return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    const allowance = value_range.contractAllowance(o) orelse return false;
    var scanner: Oracle = .{
        .gpa = o.gpa,
        .tree = tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = 0,
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .memo = o.memo,
    };
    defer scanner.deinit();
    defer value_range.inheritStop(o, &scanner);
    defer o.budget -= value_range.chargeContractSteps(allowance, &scanner);
    var effects: EffectScan = .{};
    scanEffects(&scanner, body, &effects, 0);
    if (!effects.complete or effects.call_count != 0) return false;
    for (effects.writes[0..effects.write_count]) |write| {
        if (!std.mem.startsWith(u8, write, name) or write.len <= name.len + 1 or write[name.len] != '.') return false;
        const written_field = write[name.len + 1 ..];
        if (std.mem.indexOfScalar(u8, written_field, '.') != null or std.mem.eql(u8, written_field, field)) return false;
    }
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(body);
    const last = tree.lastToken(body);
    while (token <= last) : (token += 1) {
        if (!scanner.spend()) return false;
        // A copy builtin writes the field's contents, not just its value.
        // Those contents can alias another field of this same struct.
        if (tags[token] == .builtin and !value_range.isPureBuiltin(tree.tokenSlice(token))) return false;
        if (tags[token] != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), name)) continue;
        if (token == last or tags[token + 1] != .period) return false;
    }
    return true;
}

/// A selected receiver field survives only a complete, context-keyed effect
/// proof. Canonical actual-to-formal mapping covers value and pointer receivers;
/// neither a copied value nor a const spelling proves absence of mutation.
/// Rooted and unrooted effects spend this oracle's remaining allowance. The
/// enclosing subtree scan also checks every evaluated actual expression.
fn methodSummaryKeepsField(o: *Oracle, call_node: Ast.Node.Index, receiver: Ast.Node.Index, path: []const u8) bool {
    if (o.tree.nodeTag(receiver) != .identifier) return false;
    return argumentSummaryKeepsField(o, call_node, receiver, path);
}

/// Discharge one actual's access only through its exact formal-field effect
/// and the complete unrooted effect. Other actuals are checked independently.
fn argumentSummaryKeepsField(o: *Oracle, call_node: Ast.Node.Index, argument: Ast.Node.Index, path: []const u8) bool {
    if (o.summary_error != null) return false;
    const tree = o.tree;
    const operand = value_range.unwrapGrouped(tree, argument);
    const storage = if (tree.nodeTag(operand) == .address_of)
        value_range.unwrapGrouped(tree, tree.nodeData(operand).node)
    else
        operand;
    if (!value_range.isPureFieldPath(tree, storage)) return false;
    const owner = value_range.nodeSrc(tree, storage);
    if (!std.mem.startsWith(u8, path, owner) or path.len <= owner.len + 1 or
        path[owner.len] != '.') return false;
    const field = path[owner.len + 1 ..];
    if (std.mem.indexOfAny(u8, field, "[*(") != null) return false;
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const TypeResolver = @import("../type_resolver.zig").TypeResolver;
    var call_buffer: [2]Ast.Node.Index = undefined;
    const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse return false;
    const token = call.queryToken(tree, call_node);
    const frame = o.resolution_frame orelse resolver.resolutionFrame();
    const actual = (cache.actualCallSummaryAt(token, frame) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) orelse return false;
    var parameter: u32 = 0;
    while (true) : (parameter += 1) {
        if (!o.spend()) return false;
        const mapped = (actual.callArgumentFor(cache, &call_buffer, parameter) catch |err| {
            o.summary_error = o.summary_error orelse err;
            return false;
        }) orelse return false;
        if (mapped == argument) break;
    }
    const context = @import("../cache/call_summary.zig").QueryContext{
        .frame = frame,
        .remaining = &o.budget,
        .declaration = value_range.enclosingFnDecl(o),
    };
    const effect = (cache.callEffectAt(token, .{ .parameter = .{ .param = parameter, .path = field } }, context) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) orelse return false;
    if (effect != .read_only) return false;
    const unrooted = (cache.callEffectAt(token, .unrooted, context) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) orelse return false;
    return unrooted == .read_only;
}

/// `list.ensureTotalCapacity(…)`, `list.ensureTotalCapacityPrecise(…)` and
/// `list.ensureUnusedCapacity(…)` of a `std/array_list.zig` container only
/// reallocate: they write `capacity` and `items.ptr`, never `items.len`.  So
/// a fact about `<receiver>.items.len` survives the call.  The declaration is
/// the identity — its own document and its own name, as the resolver reads
/// them — so a project method that shares the spelling and resizes the list
/// still drops the fact.  Every other path under the receiver is still
/// reached.
fn capacityMethodKeepsLength(o: *Oracle, call_node: Ast.Node.Index, receiver: Ast.Node.Index, path: []const u8) bool {
    const tree = o.tree;
    if (!value_range.isPureFieldPath(tree, receiver)) return false;
    const spelling = value_range.nodeSrc(tree, receiver);
    if (!std.mem.startsWith(u8, path, spelling) or !std.mem.eql(u8, path[spelling.len..], ".items.len")) return false;
    var call_buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, call_node) orelse return false;
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const method = tree.tokenSlice(tree.nodeData(call.ast.fn_expr).node_and_token[1]);
    if (!std.mem.eql(u8, method, "ensureTotalCapacity") and
        !std.mem.eql(u8, method, "ensureTotalCapacityPrecise") and
        !std.mem.eql(u8, method, "ensureUnusedCapacity")) return false;
    const resolver = (o.cache orelse return false).zls orelse return false;
    const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) {
        .function => |reference| reference,
        .unknown, .not_callable => return false,
    };
    const toolchain_file = resolver.declaredInToolchainFile(reference.handle, "/std/array_list.zig") catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    };
    if (!toolchain_file) return false;
    return std.mem.eql(u8, reference.tree.tokenSlice(reference.fn_token + 1), method);
}

/// The standard-library files whose container methods only write the
/// container they are called on.
const container_files = [_][]const u8{
    "/std/array_list.zig",
    "/std/hash_map.zig",
    "/std/array_hash_map.zig",
    "/std/multi_array_list.zig",
};

/// `object.a.method(…)` of a standard container hands the callee a pointer to
/// `object.a` ALONE: it writes what that container holds, and nothing in the
/// pointer names `object.b`.  So a fact about a SIBLING field path
/// (`self.path_text.items.len` under a call on `self.paths`) survives it.
/// The fact and the receiver must both be plain dotted field paths that
/// diverge below their shared root — neither lies inside the other, because
/// then the call writes the fact's own storage — and the callee's declaration
/// must be a standard container's, by document identity: a project method
/// that shares the spelling can write through anything it was given.  The
/// call's other arguments are asked on their own by the caller.
fn containerMethodKeepsSibling(o: *Oracle, call_node: Ast.Node.Index, receiver: Ast.Node.Index, path: []const u8) bool {
    const tree = o.tree;
    const spelling = value_range.nodeSrc(tree, receiver);
    if (std.mem.indexOfAny(u8, spelling, "[*(") != null or std.mem.indexOfAny(u8, path, "[*(") != null) return false;
    var receiver_segments = std.mem.splitScalar(u8, spelling, '.');
    var path_segments = std.mem.splitScalar(u8, path, '.');
    while (true) {
        const left = receiver_segments.next() orelse return false;
        const right = path_segments.next() orelse return false;
        if (!std.mem.eql(u8, left, right)) break;
    }
    var call_buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, call_node) orelse return false;
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const resolver = (o.cache orelse return false).zls orelse return false;
    const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) {
        .function => |reference| reference,
        .unknown, .not_callable => return false,
    };
    for (container_files) |file| {
        const toolchain_file = resolver.declaredInToolchainFile(reference.handle, file) catch |err| {
            o.summary_error = o.summary_error orelse err;
            return false;
        };
        if (toolchain_file) return true;
    }
    return false;
}

/// Indexed field stores are still element writes, not unknown writes to all
/// storage. Preserving an INDIRECT header additionally needs the shared
/// oracle's canonical allocation/all-origins separation fact.
fn indexedStoreContainer(o: *Oracle, target: Ast.Node.Index) ?Ast.Node.Index {
    var node = value_range.unwrapGrouped(o.tree, target);
    var depth: u8 = 0;
    while (o.tree.nodeTag(node) == .field_access) : (depth += 1) {
        if (depth == value_range.walk_depth_cap) {
            o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = value_range.walk_depth_cap });
            return null;
        }
        if (!o.spend()) return null;
        node = value_range.unwrapGrouped(o.tree, o.tree.nodeData(node).node_and_token[0]);
    }
    if (o.tree.nodeTag(node) != .array_access) return null;
    return value_range.unwrapGrouped(o.tree, o.tree.nodeData(node).node_and_node[0]);
}

/// Every field after the index must stay inside the element's storage.
/// A field on a pointer can implicitly dereference it; purity is not a
/// separation proof. Slice-header fields themselves are by-value storage.
fn indexedProjectionIsInline(o: *Oracle, target: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const frame = o.resolution_frame orelse resolver.resolutionFrame();
    var node = value_range.unwrapGrouped(o.tree, target);
    var depth: u8 = 0;
    while (o.tree.nodeTag(node) == .field_access) : (depth += 1) {
        if (depth == value_range.walk_depth_cap) {
            o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = value_range.walk_depth_cap });
            return false;
        }
        if (!o.spend()) return false;
        const base = value_range.unwrapGrouped(o.tree, o.tree.nodeData(node).node_and_token[0]);
        const actual = (frame.typeOfNode(base) catch |err| {
            o.summary_error = o.summary_error orelse err;
            return false;
        }) orelse return false;
        switch (resolver.typeTag(actual) orelse return false) {
            .@"struct", .@"union" => {},
            .pointer => if ((resolver.pointerSize(actual) orelse return false) != .slice) return false,
            else => return false,
        }
        node = base;
    }
    return o.tree.nodeTag(node) == .array_access;
}


/// True when a call at `effect` can hand the callee storage that `path` names.
/// `false` is only returned for effects we can enumerate completely: an
/// ordinary call (receiver + arguments) or the writing argument of a
/// `@memcpy`/`@memset`.  Anything else is treated as reaching everything.
///
/// An ordinary ARGUMENT is asked `argumentReaches` rather than `escapeReaches`,
/// because an `&x` argument is the one shape whose write access depends on the
/// callee and not on the spelling at the call site: the same address hands a
/// writing callee the storage and a non-writing one a value it ignores.
pub fn pathEscapedBy(o: *Oracle, effect: Ast.Node.Index, path: []const u8) bool {
    const tree = o.tree;
    // Indexed stores can alias caller-owned pointers or escaped locals. They
    // cannot change an independent frame-local index whose address never
    // leaves this body. The base spelling alone does not prove disjointness:
    // two slice/pointer parameters can name the same element.
    if (std.mem.startsWith(u8, @tagName(tree.nodeTag(effect)), "assign") and
        tree.nodeTag(effect) != .assign_destructure)
    {
        const target = tree.nodeData(effect).node_and_node[0];
        if (indexedStoreContainer(o, target)) |container| {
            if (o.effect_isolated_headers) |headers| {
                if (value_range.isPureFieldPath(tree, container)) {
                    const header = value_range.nodeSrc(tree, container);
                    if (std.mem.eql(u8, header, path) and headers.headerIsolated(header) and
                        indexedProjectionIsInline(o, target) and
                        value_range.pureIntegerExpression(o, target, 0) and
                        value_range.pureIntegerExpression(o, tree.nodeData(effect).node_and_node[1], 0)) return false;
                }
            }
            const root = rootText(path);
            return o.indirection_roots.contains(root) or o.addressed.contains(root) or
                !value_range.isLocalName(o, root);
        }
    }
    var call_buffer: [1]Ast.Node.Index = undefined;
    if (tree.fullCall(&call_buffer, effect)) |call| {
        // An escaped local or indirect storage can be reached through a
        // global pointer, even when this call passes only scalar arguments.
        // Keep its facts only if the exact callee proves no unrooted write.
        const root = rootText(path);
        if ((o.addressed.contains(root) or o.indirection_roots.contains(root) or
            !value_range.isLocalName(o, root)) and !callKeepsUnrootedStorage(o, effect))
            return true;
        if (tree.nodeTag(call.ast.fn_expr) == .field_access) {
            const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
            // Zig binds `recv.method(...)` as `method(&recv, ...)` whenever the
            // method takes a pointer receiver, so the receiver's own storage is
            // writable even though no address appears in the source.
            const overlaps = value_range.isPureFieldPath(tree, receiver) and
                pathSegmentsOverlap(value_range.nodeSrc(tree, receiver), path) and
                !containerMethodKeepsSibling(o, effect, receiver, path);
            if (overlaps and !methodKeepsField(o, effect, receiver, path) and
                !capacityMethodKeepsLength(o, effect, receiver, path) and
                !methodSummaryKeepsField(o, effect, receiver, path)) return true;
            if (!overlaps and escapeReaches(o, receiver, path)) return true;
        }
        for (call.ast.params) |param| {
            if (argumentReaches(o, effect, param, path)) return true;
        }
        return false;
    }
    var builtin_buffer: [2]Ast.Node.Index = undefined;
    if (tree.builtinCallParams(&builtin_buffer, effect)) |params| {
        const name = tree.tokenSlice(tree.nodeMainToken(effect));
        // Only the destination of a copy/set is written; the sources are read.
        if (params.len != 0 and (std.mem.eql(u8, name, "@memcpy") or std.mem.eql(u8, name, "@memset")))
            return escapeReaches(o, params[0], path);
        return true;
    }
    return true;
}

fn callKeepsUnrootedStorage(o: *Oracle, call_node: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const TypeResolver = @import("../type_resolver.zig").TypeResolver;
    var buffer: [2]Ast.Node.Index = undefined;
    const call = TypeResolver.CallOperands.full(o.tree, &buffer, call_node) orelse return false;
    const context = @import("../cache/call_summary.zig").QueryContext{
        .frame = o.resolution_frame orelse resolver.resolutionFrame(),
        .remaining = &o.budget,
        .declaration = value_range.enclosingFnDecl(o),
    };
    const effect = (cache.callEffectAt(call.queryToken(o.tree, call_node), .unrooted, context) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) orelse return false;
    return effect == .read_only;
}

/// Does this argument hand the callee storage overlapping `path`?
///
/// Pointer-bearing values can also reach escaped storage through their
/// pointees. Only a complete read-only callee certificate can discharge
/// that access; the argument's AST shape does not determine mutability.
fn argumentReaches(o: *Oracle, call_node: Ast.Node.Index, argument: Ast.Node.Index, path: []const u8) bool {
    if (!escapeReaches(o, argument, path)) return false;
    if (calleeKeepsAddress(o, call_node)) return false;
    return !argumentSummaryKeepsField(o, call_node, argument, path);
}

/// A complete effect certificate covers every formal and unrooted storage.
/// Reuse the cache's exact contextual query rather than rescanning the same
/// callee for each surviving scalar and conditional length fact.
fn calleeKeepsAddress(o: *Oracle, call_node: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const TypeResolver = @import("../type_resolver.zig").TypeResolver;
    var buffer: [2]Ast.Node.Index = undefined;
    const call = TypeResolver.CallOperands.full(o.tree, &buffer, call_node) orelse return false;
    const frame = o.resolution_frame orelse resolver.resolutionFrame();
    const effect = (cache.callEffectAt(call.queryToken(o.tree, call_node), .{ .whole = null }, .{
        .frame = frame,
        .remaining = &o.budget,
        .declaration = value_range.enclosingFnDecl(o),
    }) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    }) orelse return false;
    return effect == .read_only;
}

/// Record every call and every direct write inside `node`.
///
/// Reading a name has no effect, so a subtree made only of reads records
/// nothing and reaches nothing.  A call is recorded whole rather than
/// flattened here because `pathEscapedBy` already knows how to ask one
/// whether its receiver and arguments hand out overlapping storage — which is
/// what keeps `catch { log(self.name); }` from dropping every fact about
/// `self`, the `log` call being handed a copy rather than an address.
pub fn scanEffects(o: *Oracle, node: Ast.Node.Index, scan: *EffectScan, depth: u8) void {
    if (!scan.complete) return;
    if (depth == value_range.walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = value_range.walk_depth_cap });
        scan.complete = false;
        return;
    }
    if (!o.spend()) {
        scan.complete = false;
        return;
    }
    const tree = o.tree;
    const tag = tree.nodeTag(node);
    switch (tag) {
        .call, .call_comma, .call_one, .call_one_comma => {
            if (scan.call_count == effect_scan_cap) {
                scan.complete = false;
                return;
            }
            scan.calls[scan.call_count] = node;
            scan.call_count += 1;
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => builtin_effects: {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            if (value_range.isPureBuiltin(name)) break :builtin_effects;
            var buffer: [2]Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, node) orelse {
                scan.complete = false;
                return;
            };
            // The two copy builtins write exactly their destination, which is
            // a nameable path or nothing at all: a subscripted destination
            // cannot be spelled, and guessing at its root would understate
            // what the copy can reach.
            if (params.len != 0 and (std.mem.eql(u8, name, "@memcpy") or std.mem.eql(u8, name, "@memset"))) {
                if (!value_range.isPureFieldPath(tree, params[0]) or scan.write_count == effect_scan_cap) {
                    scan.complete = false;
                    return;
                }
                scan.writes[scan.write_count] = value_range.nodeSrc(tree, params[0]);
                scan.write_count += 1;
                break :builtin_effects;
            }
            // Any other builtin the pure list does not name may write through
            // a pointer argument, so it is recorded as a call.
            if (scan.call_count == effect_scan_cap) {
                scan.complete = false;
                return;
            }
            scan.calls[scan.call_count] = node;
            scan.call_count += 1;
        },
        .assign_destructure => {
            // Destructure targets are written in an order this scan does not
            // model, and a two-part path like `x.f[0]` is not a field path.
            scan.complete = false;
            return;
        },
        .@"asm", .asm_simple => {
            scan.complete = false;
            return;
        },
        else => plain: {
            if (!std.mem.startsWith(u8, @tagName(tag), "assign")) break :plain;
            const target = tree.nodeData(node).node_and_node[0];
            if (indexedStoreContainer(o, target) != null) {
                // Keep this as a non-leaf effect, not a direct field write.
                // Receiver purity proofs reject it through call_count, while
                // pathEscapedBy distinguishes independent local indices from
                // storage that may alias an array element.
                if (scan.call_count == effect_scan_cap) {
                    scan.complete = false;
                    return;
                }
                scan.calls[scan.call_count] = node;
                scan.call_count += 1;
                break :plain;
            }
            if (!value_range.isPureFieldPath(tree, target)) {
                if (tree.nodeTag(target) != .deref or scan.write_count == effect_scan_cap) {
                    scan.complete = false;
                    return;
                }
                const pointer = value_range.unwrapGrouped(tree, tree.nodeData(target).node);
                if (tree.nodeTag(pointer) != .identifier or
                    !o.pointer_roots.contains(tree.tokenSlice(tree.nodeMainToken(pointer))))
                {
                    scan.complete = false;
                    return;
                }
                scan.write_pointers[scan.write_count] = pointer;
                scan.writes[scan.write_count] = value_range.nodeSrc(tree, pointer);
                scan.write_count += 1;
                break :plain;
            }
            if (scan.write_count == effect_scan_cap) {
                scan.complete = false;
                return;
            }
            if (tree.nodeTag(target) == .field_access) {
                var root = target;
                while (tree.nodeTag(root) == .field_access) root = tree.nodeData(root).node_and_token[0];
                if (tree.nodeTag(root) == .identifier and
                    hasFreshStorage(o, tree.tokenSlice(tree.nodeMainToken(root)), tree.firstToken(node)))
                {
                    // Different local spellings can name the same allocation.
                    // Charge this store to that storage, not only its spelling.
                    scan.write_pointers[scan.write_count] = root;
                }
            }
            scan.writes[scan.write_count] = value_range.nodeSrc(tree, target);
            scan.write_count += 1;
        },
    }
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| scanEffects(o, child, scan, depth + 1);
}

/// Does this argument hand the callee storage overlapping `path`? An address
/// names its write target; a pointer variable names its resolved pointee.
/// A projection is a copy of its value, which can itself carry pointers.
fn escapeReaches(o: *Oracle, operand: Ast.Node.Index, path: []const u8) bool {
    const tree = o.tree;
    const arg = value_range.unwrapGrouped(tree, operand);
    switch (tree.nodeTag(arg)) {
        .address_of => return pathSegmentsOverlap(
            value_range.nodeSrc(tree, value_range.unwrapGrouped(tree, tree.nodeData(arg).node)),
            path,
        ),
        .identifier => {
            const name = tree.tokenSlice(tree.nodeMainToken(arg));
            if (!o.pointer_roots.contains(name)) return false;
            // The chain is composed into a STACK buffer, not minted: this runs
            // once per fact per effect, and a chain with no spelling that fits
            // falls through to the conservative answer below rather than
            // truncating to a partial one.
            var suffixes: [alias_hop_cap][]const u8 = undefined;
            const chain = resolveAliasChain(o, name, tree.firstToken(arg), &suffixes);
            if (chain.fresh_token) |allocation| {
                const other_root = rootText(path);
                if (!o.pointer_roots.contains(other_root)) return false;
                var other_suffixes: [alias_hop_cap][]const u8 = undefined;
                const other = resolveAliasChain(o, other_root, tree.firstToken(arg), &other_suffixes);
                if (other.fresh_token) |other_allocation| return allocation == other_allocation;
                // A parameter's object existed before this allocation; an
                // unresolved local factory result may instead alias it.
                return other.unresolved;
            }
            var buffer: [256]u8 = undefined;
            if (composeAliasPath(chain, &buffer)) |target| {
                return pathSegmentsOverlap(target, path);
            }
            // No binding in this body establishes what this pointer names, so
            // "the call may write anything" is the answer for storage this
            // body knows nothing about.  There are two kinds of "pointer"
            // here and they answer differently.
            //
            // A root that HOLDS AN ADDRESS — `indirection_roots` — is aimed at
            // storage that already existed when the frame was created, so the
            // callee may write through it whatever it was aimed at: `f(holder)`
            // can rewrite `holder.index`, and a fact about that field does not
            // survive. A parameter cannot name an unescaped frame-local slot,
            // but can alias another pointer parameter's backing storage.
            if (o.indirection_roots.contains(name)) {
                if (isParameterRoot(o, name) and !std.mem.eql(u8, rootText(path), name)) {
                    return o.addressed.contains(rootText(path)) or
                        o.indirection_roots.contains(rootText(path));
                }
                return true;
            }
            //
            // A root that is pointer-LIKE but is NOT an address is a BY-VALUE
            // header: a slice, an array or a struct passed or returned by
            // value.  The header lives in the local's own frame slot and the
            // callee receives a COPY of it, so nothing the callee does can
            // resize the local or replace the slice in that slot — it can
            // write the ELEMENTS the header points at, and an element write is
            // not a write to the length this module records.  The one thing
            // that can rewrite the slot is its address leaving this body, and
            // `addressed` is exactly the record of that.  This is the same
            // test the parameter rule one branch up uses, generalised from
            // "is this a parameter" to "does this name hold an address", which
            // is the distinction that decides whether a copy is involved.
            return o.addressed.contains(rootText(path)) or
                o.indirection_roots.contains(rootText(path));
        },
        .field_access, .deref, .array_access => {
            if (projectionIsScalar(o, arg)) return false;
            // The projection's spelling names the slot containing the pointer,
            // not its pointee. Unknown and pointer-bearing values may reach any
            // indirect or escaped storage, but not an unaddressed local header.
            const root = rootText(path);
            return o.indirection_roots.contains(root) or o.addressed.contains(root) or
                !value_range.isLocalName(o, root);
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            var buffer: [2]Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, arg) orelse return true;
            const name = tree.tokenSlice(tree.nodeMainToken(arg));
            if (params.len == 1 and (std.mem.eql(u8, name, "@constCast") or
                std.mem.eql(u8, name, "@ptrCast") or std.mem.eql(u8, name, "@alignCast") or
                std.mem.eql(u8, name, "@addrSpaceCast") or std.mem.eql(u8, name, "@volatileCast")))
                return escapeReaches(o, params[0], path);
            if (params.len == 2 and std.mem.eql(u8, name, "@as"))
                return escapeReaches(o, params[1], path);
            if (projectionIsScalar(o, arg)) return false;
            // An unmodeled pointer-producing expression cannot prove that
            // storage is unreachable.
            return o.indirection_roots.contains(rootText(path)) or o.addressed.contains(rootText(path));
        },
        else => return false,
    }
}

/// Only a resolved primitive proves a projected value carries no pointers.
/// Aggregates, slices and unresolved types cannot establish that proof.
fn projectionIsScalar(o: *Oracle, node: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const frame = o.resolution_frame orelse resolver.resolutionFrame();
    const resolved = frame.typeOfNode(node) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    };
    const ty = resolved orelse return false;
    return switch (resolver.typeTag(ty) orelse return false) {
        .bool, .@"enum", .int, .comptime_int, .float, .comptime_float => true,
        else => false,
    };
}

/// Leading identifier of a source-spelled path (`self` from `self.items[0]`).
pub fn rootText(path: []const u8) []const u8 {
    var end: usize = 0;
    while (end < path.len and path[end] != '.' and path[end] != '[') : (end += 1) {}
    return path[0..end];
}

/// True when a CALLEE handed one of these paths can write the storage the
/// other names.  The granularity is the ROOT, because the callee receives a
/// pointer to the object and nothing in the source says which field of it
/// it will touch: `&holder` reaches `holder.text`, `holder.count` and every
/// other field alike.
fn pathSegmentsOverlap(a: []const u8, b: []const u8) bool {
    const left = rootText(a);
    const right = rootText(b);
    var i: usize = 0;
    var j: usize = 0;
    while (true) {
        const l = nextSegment(left, &i) orelse return true;
        const r = nextSegment(right, &j) orelse return true;
        if (!std.mem.eql(u8, l, r)) return false;
    }
}

/// True when a DIRECT write to `write` lands on the storage `path` names.
///
/// A store names one location, so the whole path is compared segment by
/// segment and the answer is decided at the first segment that differs.
/// `holder.count = 0` writes `count` and leaves `holder.text` alone: the two
/// share a root, but a guard about one of them says nothing about the other,
/// and dropping it anyway would report a read the source cannot reach with
/// an empty slice.  A path that runs out first is a prefix of the other
/// (`holder.text` vs `holder.text.len`), and a write to it does land on the
/// longer one.
fn writeReachesPath(write: []const u8, path: []const u8) bool {
    var i: usize = 0;
    var j: usize = 0;
    while (true) {
        const w = nextSegment(write, &i) orelse return true;
        const p = nextSegment(path, &j) orelse return true;
        if (!std.mem.eql(u8, w, p)) return false;
    }
}

fn nextSegment(path: []const u8, cursor: *usize) ?[]const u8 {
    if (cursor.* >= path.len) return null;
    var end = cursor.*;
    while (end < path.len and path[end] != '.') : (end += 1) {}
    const segment = path[cursor.*..end];
    cursor.* = if (end < path.len) end + 1 else end;
    return segment;
}

/// What a write spelled `path` ALSO lands on, when its root is a pointer.
///
/// A pointer's own spelling is not where the write goes.  `p.count = 0` writes
/// `(*p).count`, and this is the step that says which storage `(*p)` is — which
/// is a CHAIN of pointer bindings, followed here to its end through every
/// binding in force at `at`.  A two-hop body therefore reaches what the chain
/// reaches, not only the first link of it.
///
/// The chain keeps whatever projection each binding carries.  `const p =
/// &holder.count` names `holder.count` and not `holder`, so a write through
/// `p` invalidates the facts about that one field instead of every fact about
/// the struct.
///
/// Identity is the BINDING, not the name, and each hop is read as of the token
/// that captured it rather than as of the store being analysed.  In `var p =
/// &first; const q = p; p = &second;` the name `q` took `p`'s value while `p`
/// was still `&first`, so the chain has to resolve `p` as of that binding and
/// reach `first` — resolving every hop at the store would name `second`,
/// invalidating storage the write never touches while keeping the storage it
/// does.  `latestEscapeBinding` returns the last binding strictly before the
/// anchor together with that binding's own token, and the anchor moves to it;
/// a second local of the same name in a sibling block is read the same way,
/// through the binding in force at the anchor rather than the first spelled.
///
/// `.unknown` is the answer whenever the chain does not end, and it is what
/// keeps the failure direction sound.  A binding this body recorded but could
/// not resolve, a chain past the cap and a cycle all mean the same thing — the
/// write may land on storage this body never named — so the facts it could
/// reach are dropped rather than kept on the strength of an alias the walk
/// could not follow.
///
/// A chain that ended at a name this body never bound — a pointer PARAMETER, or
/// a parameter with no type spelling — is not the same as a chain that did not
/// end.  Its target is in the CALLER's frame, so it cannot name a fresh local
/// of this body; but two parameters may be handed the same object, so it CAN
/// name another parameter's storage, and it can name any local whose address
/// this body handed out.  `.parameters` is answered by that whole set and by
/// nothing else, which is what keeps an unrelated local's bound standing
/// through a method that writes through `self`.
const AliasTarget = union(enum) {
    /// The root is not a pointer, so no other spelling can be written.
    none,
    /// The chain ended at exactly one storage, projection included.
    storage: []const u8,
    /// The chain ended at a name this body never bound; the answer is a set.
    parameters: void,
    /// The chain did not end; anything the state knows may be written.
    unknown: void,
};

fn aliasedTarget(o: *Oracle, path: []const u8, at: Ast.TokenIndex) error{OutOfMemory}!AliasTarget {
    const root = rootText(path);
    if (!o.pointer_roots.contains(root)) return .none;
    var suffixes: [alias_hop_cap][]const u8 = undefined;
    const chain = resolveAliasChain(o, root, at, &suffixes);
    if (chain.unresolved) return .unknown;
    if (chain.unbound) {
        // The projections collected on the way here are still part of the
        // answer, but they cannot be applied to a set of names, so the set is
        // asked directly: `const b = &a.count` over a parameter `a` reaches
        // `a.count`, and `a.count` is itself spelled on a pointer root.
        return .parameters;
    }
    const storage = try mintAliasPath(o, chain);
    if (storage.len == 0) return .unknown;
    return .{ .storage = storage };
}

/// Invalidate everything a write spelled `name` reaches besides `name` itself.
///
/// Called only for a store that goes THROUGH the name — `p.field = v`,
/// `p.* = v`, `p[i] = v`.  A bare rebind of a pointer (`p = other`) replaces
/// which storage `p` names and writes none of it, so it never comes here.
pub fn dropAliasedStorage(o: *Oracle, st: *State, name: []const u8, at: Ast.TokenIndex) error{OutOfMemory}!void {
    var suffixes: [alias_hop_cap][]const u8 = undefined;
    const chain = resolveAliasChain(o, rootText(name), at, &suffixes);
    if (chain.fresh_token) |allocation| {
        for (o.pointer_roots.keys.items) |root| {
            var other_suffixes: [alias_hop_cap][]const u8 = undefined;
            const other = resolveAliasChain(o, root, at, &other_suffixes);
            if (other.unresolved or other.fresh_token == allocation) {
                value_range.dropFactsForRebind(o, st, root);
            }
        }
        return;
    }
    switch (try aliasedTarget(o, name, at)) {
        .none => {},
        .storage => |storage| value_range.dropFactsForRebind(o, st, storage),
        .parameters => {
            // Everything that could be behind a pointer aimed before this frame
            // existed: every indirection root — two may name one object — and
            // every name whose address this body handed out, which is the only
            // way a local can end up on the far side of a parameter.  A fresh
            // unaddressed local is not in either set and cannot be behind one,
            // which is the frame-lifetime invariant that makes this narrower
            // than a full-state drop and still sound.
            // A by-value slice header is not indirect storage: aliases can
            // change its elements but cannot replace its local length.
            for (o.indirection_roots.keys.items) |root| value_range.dropFactsForRebind(o, st, root);
            for (o.addressed.keys.items) |root| value_range.dropFactsForRebind(o, st, root);
        },
        // The chain did not end, so this write may land on anything the state
        // knows about.  Dropping it all is the sound direction and the only
        // one available: the facts at risk are keyed on storage the walk could
        // not name at all, so no set derived from the names it does know is
        // guaranteed to contain them.
        .unknown => value_range.dropIndirectFacts(o, st, .unknown),
    }
}

test "failed escape resolver queries are errors rather than missing proofs" {
    const resolver_mod = @import("../type_resolver.zig");
    const gpa = std.testing.allocator;
    const Query = enum { address, field, capacity, sibling, callee, capacity_identity, sibling_identity, first_error };
    for (std.enums.values(Query)) |query| {
        var context: resolver_mod.TypeContext = undefined;
        try context.init(gpa, std.testing.io);
        defer context.deinit();
        var resolver: resolver_mod.TypeResolver = undefined;
        try resolver.init(&context, gpa, "/tmp/zbc-numeric-escape-query-error.zig",
            \\const Box = struct {
            \\    count: usize,
            \\    items: []u8,
            \\    fn ensureTotalCapacity(self: *Box, n: usize) void { _ = self; _ = n; }
            \\};
            \\const Outer = struct { a: Box, b: Box };
            \\fn f(holder: *Box, object: *Outer) void {
            \\    _ = holder;
            \\    holder.ensureTotalCapacity(1);
            \\    object.a.ensureTotalCapacity(1);
            \\    touch(&holder);
            \\}
            \\fn touch(value: **Box) void { _ = value; }
        );
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
        var cache = file_cache_mod.FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        var oracle: Oracle = .{
            .gpa = gpa,
            .tree = tree,
            .body = .root,
            .query = .numeric_range,
            .target = "",
            .use_token = 0,
            .cache = &cache,
        };
        defer oracle.deinit();

        var selected: ?Ast.Node.Index = null;
        for (0..tree.nodes.len) |index| {
            const node: Ast.Node.Index = @enumFromInt(index);
            if (query == .address or query == .first_error) {
                if (tree.nodeTag(node) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "holder"))
                {
                    selected = node;
                    break;
                }
            } else {
                var buffer: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, node) orelse continue;
                const wanted = switch (query) {
                    .field, .capacity, .capacity_identity => "holder.ensureTotalCapacity",
                    .sibling, .sibling_identity => "object.a.ensureTotalCapacity",
                    .callee => "touch",
                    .address, .first_error => unreachable,
                };
                if (std.mem.eql(u8, value_range.nodeSrc(tree, call.ast.fn_expr), wanted)) {
                    selected = node;
                    break;
                }
            }
        }
        const node = selected orelse return error.TestUnexpectedResult;
        if (query == .first_error) oracle.summary_error = error.SourceExcluded;
        const identity = query == .capacity_identity or query == .sibling_identity;
        // Fail only query allocations, after the document and oracle exist.
        // Cold types need the analyser arena. Identity queries use a URI that
        // exceeds their stack scratch, so only their fallback allocator fails.
        var long_uri: ?[]u8 = null;
        defer if (long_uri) |uri| gpa.free(uri);
        const original_uri = resolver.handle.document.uri;
        defer resolver.handle.document.uri = original_uri;
        if (identity) {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node).?;
            const reference = try resolver.functionReference(call.ast.fn_expr);
            try std.testing.expect(reference == .function);
            long_uri = try gpa.alloc(u8, std.Io.Dir.max_path_bytes + 32);
            @memcpy(long_uri.?[0..8], "file:///");
            @memset(long_uri.?[8..], 'a');
            resolver.handle.document.uri = .{ .raw = long_uri.? };
        }
        var failing: std.testing.FailingAllocator = .init(
            if (identity) resolver.gpa else resolver.analyser.arena.allocator(),
            .{ .fail_index = 0 },
        );
        // Start empty so any analyser allocation reaches the failing child.
        var failing_arena: std.heap.ArenaAllocator = .init(failing.allocator());
        defer failing_arena.deinit();
        const arena = resolver.analyser.arena;
        const resolver_gpa = resolver.gpa;
        defer resolver.analyser.arena = arena;
        defer resolver.gpa = resolver_gpa;
        if (identity) {
            resolver.gpa = failing.allocator();
        } else {
            resolver.analyser.arena = &failing_arena;
        }
        const answer = switch (query) {
            .address, .first_error => valueIsAddress(&oracle, node),
            .field, .capacity, .sibling, .capacity_identity, .sibling_identity => blk: {
                var buffer: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, node).?;
                const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                break :blk switch (query) {
                    .field => methodKeepsField(&oracle, node, receiver, "holder.count"),
                    .capacity, .capacity_identity => capacityMethodKeepsLength(&oracle, node, receiver, "holder.items.len"),
                    .sibling, .sibling_identity => containerMethodKeepsSibling(&oracle, node, receiver, "object.b.items.len"),
                    else => unreachable,
                };
            },
            .callee => calleeKeepsAddress(&oracle, node),
        };
        try std.testing.expect(!answer);
        try std.testing.expect(failing.has_induced_failure);
        const expected: value_range.QueryError = if (query == .first_error) error.SourceExcluded else error.OutOfMemory;
        try std.testing.expectEqual(@as(?value_range.QueryError, expected), oracle.summary_error);
        var state: State = .{};
        defer state.deinit(gpa);
        try std.testing.expectError(expected, value_range.analyzeNode(&oracle, node, &state));
    }
}

test "successful unresolved escape queries remain no proof without an error" {
    const resolver_mod = @import("../type_resolver.zig");
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-numeric-escape-query-unknown.zig",
        \\fn f() void { _ = missing; unknown(); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var oracle: Oracle = .{
        .gpa = gpa,
        .tree = tree,
        .body = .root,
        .query = .numeric_range,
        .target = "",
        .use_token = 0,
        .cache = &cache,
    };
    defer oracle.deinit();
    var addressed = false;
    var called = false;
    for (0..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "missing"))
        {
            try std.testing.expect(!valueIsAddress(&oracle, node));
            addressed = true;
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, node) != null) {
            try std.testing.expect(!calleeKeepsAddress(&oracle, node));
            called = true;
        }
    }
    try std.testing.expect(addressed and called);
    try std.testing.expectEqual(@as(?value_range.QueryError, null), oracle.summary_error);
}

test "receiver field preservation requires canonical rooted unrooted and actual effects" {
    const resolver_mod = @import("../type_resolver.zig");
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-numeric-receiver-field-effects.zig",
        \\var escaped: i16 = 0;
        \\extern fn foreign() void;
        \\const Box = struct {
        \\    count: i16,
        \\    fn read(self: @This()) void { _ = self.count; }
        \\    fn readConst(self: *const @This()) void { self.read(); }
        \\    fn write(self: *@This()) void { self.count = -32768; }
        \\    fn writeGlobal(self: @This()) void { _ = self; escaped = -32768; }
        \\    fn opaqueCall(self: @This()) void { _ = self; foreign(); }
        \\    fn readAfter(self: @This(), marker: bool) void { _ = self.count; _ = marker; }
        \\};
        \\fn touch(value: *Box) bool { value.count = -32768; return true; }
        \\fn f(value: Box) void {
        \\    var holder = value;
        \\    holder.read();
        \\    holder.readConst();
        \\    holder.write();
        \\    holder.writeGlobal();
        \\    holder.opaqueCall();
        \\    holder.readAfter(touch(&holder));
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const cases = .{
        .{ "holder.read", true },
        .{ "holder.readConst", true },
        .{ "holder.write", false },
        .{ "holder.writeGlobal", false },
        .{ "holder.opaqueCall", false },
        .{ "holder.readAfter", false },
    };
    inline for (cases) |case| {
        var selected: ?Ast.Node.Index = null;
        for (0..tree.nodes.len) |index| {
            const node: Ast.Node.Index = @enumFromInt(index);
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse continue;
            if (std.mem.eql(u8, value_range.nodeSrc(tree, call.ast.fn_expr), case[0])) {
                selected = node;
                break;
            }
        }
        const node = selected orelse return error.TestUnexpectedResult;
        const declaration = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse
            return error.TestUnexpectedResult;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse
            return error.TestUnexpectedResult;
        const body = tokens.bodyOf(tree, declaration) orelse return error.TestUnexpectedResult;
        var oracle: Oracle = .{
            .gpa = gpa,
            .tree = tree,
            .body = body,
            .query = .numeric_range,
            .target = "",
            .use_token = tree.firstToken(node),
            .cache = &cache,
            .locals = (try cache.localBindings(proto, body)).items,
        };
        defer oracle.deinit();
        try collectEscapeRoots(&oracle);
        try std.testing.expectEqual(case[1], pathSurvivesCall(&oracle, "holder.count", .{ .subtree = node }));
        try std.testing.expectEqual(@as(?value_range.QueryError, null), oracle.summary_error);
    }
}
