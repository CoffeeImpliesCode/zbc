//! `.allocator().free(x)` on a `std.heap.ArenaAllocator` whose most
//! recent allocation is NOT the slice being freed.
//!
//! The pinned standard library is the whole premise, so it is read
//! before anything is claimed.  `std.heap.ArenaAllocator` hands out an
//! allocator whose `free` compares the end of the slice it was given
//! against the arena's bump cursor and, ONLY when the two are the same
//! address, rewinds that cursor over the slice; every other slice is
//! returned over having reclaimed nothing.  Freeing the slice you just
//! allocated is therefore a real release — the case a user is most
//! likely to be looking at when they ask whether their memory came
//! back.  A rule that calls the call a no-op is wrong there, and a fix
//! that says "delete it" throws away a reclaim that was happening.
//!
//! So the rule reports the one shape it can prove, and stays silent on
//! the rest:
//!
//!   NO RECLAIM — reported.  The `.allocator()` receiver is read as a
//!   `std.heap.ArenaAllocator` through the type expression its own
//!   declaration writes, the freed slice is an allocation that same
//!   arena made, and another allocation with provably nonzero storage
//!   from that arena is written straight-line between the two.  The
//!   cursor has moved past the slice, so the call releases nothing.
//!
//!   LAST REWIND — silent.  The same, with nothing written between the
//!   two that can move the cursor.  The freed slice is still the arena's
//!   most recent allocation, and `free` releases it.
//!
//!   UNKNOWN — silent.  Everything else: a receiver whose declared type
//!   this file does not write out, a freed expression that is not a
//!   name bound here, a branch, a block, a repeat or a nested function
//!   between the allocation and the free, an allocation whose byte
//!   count is unknown, or any other call written between them. None
//!   of those settle which of the two real
//!   behaviours applies.  An unknown is NOT downgraded to an advisory:
//!   arena code is full of `.allocator().free(...)` this rule has no
//!   opinion about, and a finding on every one of them is noise, not
//!   analysis.
//!
//! NO NAME DECIDES ANYTHING.  `arena`, `ArenaState` and `scratch_pool`
//! are read the same way, and a project type that happens to be called
//! `ArenaAllocator` — with a `free` that really releases — is not the
//! library type and is not reported.  A receiver this run cannot place
//! is silent, where an earlier spelling proxy fired on the word "arena".
//!
//! Outside what the walk can answer: an arena reached through a field
//! whose declared type is written in another file, a `free` written on
//! an `Allocator` value held in a local (`const a = arena.allocator();
//! a.free(x)`), and `std.heap.FixedBufferAllocator`, whose `free` has
//! the same most-recent-only shape but is not this rule's type.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const file_model = @import("../../model/file_model.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const std_type_query = @import("../../model/std_type_query.zig");
const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "arena-allocator-free-noop";

/// Alias hops one receiver's declared type may take before the chain
/// stops being one a person wrote.
const max_alias_hops = 8;

/// An inclusive token range of the document being read.
const Range = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .arena_allocator_free_noop)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    if (last < first + 6) return;

    const bindings = cache.localBindings(proto, body) catch return;
    // Only a field path needs the file model, so a file this build
    // cannot model still answers for a plain local or parameter.
    const model = cache.fileModel() catch null;

    var t: Ast.TokenIndex = first;
    while (t + 6 <= last) : (t += 1) {
        // A nested function is its own scope with its own bindings, and
        // the walk over it is this rule's own iteration.
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        // `. allocator ( ) . free (` — the chained accessor form, which
        // is the only one this rule reads.
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t + 1), "allocator")) continue;
        if (tags[t + 2] != .l_paren or tags[t + 3] != .r_paren) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t + 5), "free")) continue;
        if (tags[t + 6] != .l_paren) continue;

        // The receiver is the dotted path written before `.allocator()`.
        if (t <= first) continue;
        const recv_end = t - 1;
        if (tags[recv_end] != .identifier) continue;
        var arena_first = recv_end;
        while (arena_first >= first + 2 and
            tags[arena_first - 1] == .period and
            tags[arena_first - 2] == .identifier)
        {
            arena_first -= 2;
        }
        const arena_last = recv_end;
        if (!isStdArenaReceiver(cache, model, bindings, tree, tags, arena_first, arena_last)) continue;

        // The freed slice is written as one bare name; a call, a field
        // or a slice expression says nothing this walk can read.
        const close = tokens.matchParen(tags, t + 6, last) orelse continue;
        const arg = t + 7;
        if (close != arg + 1 or tags[arg] != .identifier) continue;

        const effect = classify(tree, tags, bindings, arena_first, arena_last, arg, last);
        if (effect != .no_reclaim) continue;
        try report(gpa, problems, tree, t + 1, tree.tokenSlice(arg));
    }
}

/// What one `.allocator().free(x)` call site settles about itself.
const FreeEffect = enum {
    /// A provably positive-sized allocation from this arena is written
    /// after the freed one, so `free` reclaims nothing.
    no_reclaim,
    /// Nothing written after the allocation can move the cursor, so
    /// the freed slice is still the arena's most recent allocation and
    /// `free` really does release it.
    last_rewind,
    /// This document does not say which of the two it is.
    unknown,
};

fn classify(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    arena_first: Ast.TokenIndex,
    arena_last: Ast.TokenIndex,
    arg: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
) FreeEffect {
    const slice = tree.tokenSlice(arg);
    const binding = bindings.findAt(slice, arg) orelse return .unknown;
    const call = binding.asCall() orelse return .unknown;

    // The slice has to be memory THIS arena handed out: the same
    // receiver path, `.allocator()`, and a method that gives the arena
    // more memory.
    const made = arenaCallAt(tree, tags, call.receiver_token, binding.rhs_last, arena_first, arena_last) orelse return .unknown;
    if (allocationAdvancesCursor(tree, tags, made, binding.rhs_last) != true) return .unknown;

    // Everything from the end of the allocation statement to the free's
    // own receiver is what could have changed since.
    var end = binding.rhs_last;
    while (end < body_last and tags[end] != .semicolon) : (end += 1) {}
    if (end >= body_last) return .unknown;
    const from = end + 1;
    if (from > arena_first) return .unknown;

    // A second mention of the name in between could be a rebinding, and
    // then the slice the free is handed is not this allocation.
    for (tags[from..arena_first], from..) |tag, index| {
        if (tag != .identifier) continue;
        const tok: Ast.TokenIndex = @intCast(index);
        if (std.mem.eql(u8, tree.tokenSlice(tok), slice)) return .unknown;
    }

    return classifyWindow(tree, tags, arena_first, arena_last, from, arena_first -| 1);
}

/// Read the tokens between an arena allocation and the `free` that
/// gives its slice back, and answer only for the two shapes that are
/// decidable here: a straight line of allocations from this arena and
/// nothing else, or no call at all.
fn classifyWindow(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    arena_first: Ast.TokenIndex,
    arena_last: Ast.TokenIndex,
    from: Ast.TokenIndex,
    to: Ast.TokenIndex,
) FreeEffect {
    var minted = false;
    var t = from;
    while (t <= to) : (t += 1) {
        switch (tags[t]) {
            // A branch, a block, a repeat or an optional between the
            // two means the allocation written there is not one every
            // path to the free has made.
            .l_brace,
            .r_brace,
            .keyword_if,
            .keyword_else,
            .keyword_orelse,
            .keyword_catch,
            .keyword_switch,
            .keyword_while,
            .keyword_for,
            .question_mark,
            => return .unknown,

            .keyword_fn => {
                // A nested function is a body of its own that this
                // window never enters.
                t = tokens.skipNestedFn(tags, t, to);
                continue;
            },

            .identifier => {
                const call = arenaCallAt(tree, tags, t, to, arena_first, arena_last) orelse continue;
                // A `free`, a `resize` or a `realloc` written on this
                // arena in between can put the cursor BACK where it
                // was, so only an allocation settles the direction.
                const advances = allocationAdvancesCursor(tree, tags, call, to) orelse return .unknown;
                const close = tokens.matchParen(tags, call.open, to) orelse return .unknown;
                minted = minted or advances;
                t = close;
            },

            // Any other call could reach this arena through an
            // `Allocator` value this walk cannot see.
            .l_paren => return .unknown,

            else => {},
        }
    }
    // At least one call provably consumed storage, and every other
    // call either did too or provably consumed zero bytes; otherwise
    // the cursor still ends at the original slice.
    return if (minted) .no_reclaim else .last_rewind;
}

/// `<arena path> . allocator ( ) . <method> (` written at `start`,
/// when `start` opens with the same dotted path as
/// `arena_first..arena_last`.
const ArenaCall = struct {
    method: []const u8,
    open: Ast.TokenIndex,
};

fn arenaCallAt(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    limit: Ast.TokenIndex,
    arena_first: Ast.TokenIndex,
    arena_last: Ast.TokenIndex,
) ?ArenaCall {
    if (arena_last < arena_first or start > limit) return null;
    // Both paths are `identifier ( . identifier )*`, so they are walked
    // two tokens at a time and have to be the same length.  The whole
    // shape is inside `limit` before a token of it is read.
    const segments: Ast.TokenIndex = (arena_last - arena_first) / 2 + 1;
    if (start + 2 * segments + 6 > limit) return null;
    var x = start;
    var y = arena_first;
    for (0..segments) |_| {
        if (tags[x] != .identifier or tags[y] != .identifier) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(x), tree.tokenSlice(y))) return null;
        x += 2;
        y += 2;
    }
    if (tags[x] != .period) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(x + 1), "allocator")) return null;
    if (tags[x + 2] != .l_paren or tags[x + 3] != .r_paren) return null;
    if (tags[x + 4] != .period or tags[x + 5] != .identifier) return null;
    if (tags[x + 6] != .l_paren) return null;
    return .{ .method = tree.tokenSlice(x + 5), .open = x + 6 };
}

/// Prove cursor direction from the actual allocation arguments, not
/// the method name. Zero-byte allocations bypass the arena's vtable.
/// Unknown sizes/types and resize/realloc/remap stay unknown.
fn allocationAdvancesCursor(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    call: ArenaCall,
    limit: Ast.TokenIndex,
) ?bool {
    const close = tokens.matchParen(tags, call.open, limit) orelse return null;
    const type_tok = call.open + 1;
    if (type_tok >= close or tags[type_tok] != .identifier) return null;
    const element_has_storage = builtinHasStorage(tree.tokenSlice(type_tok));
    if (std.mem.eql(u8, call.method, "create")) {
        if (close != type_tok + 1) return null;
        return element_has_storage;
    }
    // Other allocating methods have different sentinel/alignment/size
    // semantics. A method-name match alone supplies no size proof.
    if (!std.mem.eql(u8, call.method, "alloc")) return null;
    if (close != type_tok + 3 or tags[type_tok + 1] != .comma or
        tags[type_tok + 2] != .number_literal) return null;
    const count = std.fmt.parseInt(u64, tree.tokenSlice(type_tok + 2), 0) catch return null;
    if (count == 0) return false;
    return element_has_storage;
}

/// These language builtin types have storage independent of the
/// document's declarations. A project type/alias needs an actual size
/// query, so it is unknown here, never presumed nonzero.
fn builtinHasStorage(name: []const u8) ?bool {
    if (std.mem.eql(u8, name, "bool") or
        std.mem.eql(u8, name, "usize") or std.mem.eql(u8, name, "isize") or
        std.mem.eql(u8, name, "f16") or std.mem.eql(u8, name, "f32") or
        std.mem.eql(u8, name, "f64") or std.mem.eql(u8, name, "f80") or
        std.mem.eql(u8, name, "f128")) return true;
    if (name.len < 2 or (name[0] != 'u' and name[0] != 'i')) return null;
    // Integer type spellings use decimal digits, not number-literal
    // syntax; reject a project identifier such as `u_8`.
    for (name[1..]) |digit| {
        if (digit < '0' or digit > '9') return null;
    }
    const bits = std.fmt.parseInt(u64, name[1..], 10) catch return null;
    return bits != 0;
}

/// Does the value `.allocator()` was written on really hold a
/// `std.heap.ArenaAllocator`?
///
/// Read from the DECLARED type, never from a name: a parameter's own
/// type, the `T` of `const x: T = …`, a field's declared type reached
/// one segment at a time through the types this file declares, or a
/// value built by the pinned `std.heap.ArenaAllocator.init`.  A type
/// written any other way — directly, through a namespace, through an
/// alias — is the same answer, because the library's own walk follows
/// the declarations either way.
fn isStdArenaReceiver(
    cache: *file_cache_mod.FileCache,
    model: ?*const file_model.FileModel,
    bindings: *const local_bindings.LocalBindings,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const root = bindings.findAt(tree.tokenSlice(first), first) orelse return false;

    if (first == last) {
        if (declaredTypeRange(tree, tags, bindings, root, 0)) |range| {
            if (namesStdArena(cache, tree, range.first, range.last)) return true;
        }
        return builtByArenaConstructor(cache, tree, tags, root);
    }

    // A field path.  Every segment is read from the type the segment
    // before it declares, and the LAST field's declared type is the one
    // that decides; a chain that leaves this file's declarations is a
    // refusal, not a yes.
    const file = model orelse return false;
    const root_range = declaredTypeRange(tree, tags, bindings, root, 0) orelse return false;
    const root_name = declaredTypeName(tree, root_range.first, root_range.last) orelse return false;
    var current = file.findType(root_name) orelse return false;
    var decided: ?Range = null;
    var seg = first + 1;
    while (seg < last) {
        if (tags[seg] != .period or tags[seg + 1] != .identifier) return false;
        const field = current.findField(tree.tokenSlice(seg + 1)) orelse return false;
        decided = .{ .first = field.type_first, .last = field.type_last };
        if (seg + 2 > last) break;
        current = file.resolveFieldTypeQualifiedTi(current, field.name) orelse return false;
        seg += 2;
    }
    const final = decided orelse return false;
    return namesStdArena(cache, tree, final.first, final.last);
}

fn namesStdArena(cache: *file_cache_mod.FileCache, tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    return std_type_query.isType(cache, tree, first, last, "heap", "ArenaAllocator", .{
        .allow_pointer = true,
    });
}

/// The declaration a type expression names: the LAST identifier of the
/// dotted path over `[first, last]`, with leading `?` / `*` / `const` /
/// `volatile` qualifiers stripped.  `Name`, `*Name`, `?*const Name` and
/// `ns.Name` all answer with `Name` — the spelling `FileModel.findType`
/// resolves — while a slice, an array, a call or anything else in the
/// range names no single declaration and is declined.
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

/// The type expression a binding's VALUE was declared with: a
/// parameter's own type, the `T` of `const x: T = …`, or — for a
/// binding that is nothing but another name — the type that name was
/// declared with.
fn declaredTypeRange(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    hops: u8,
) ?Range {
    if (hops > max_alias_hops) return null;
    if (binding.origin == .param) {
        // `fn f(x: anytype)` records the name as its own range.
        if (binding.rhs_first == binding.name_token) return null;
        return .{ .first = binding.rhs_first, .last = binding.rhs_last };
    }
    if (binding.name_token < binding.rhs_first) {
        var t = binding.name_token + 1;
        while (t < binding.rhs_first) : (t += 1) {
            if (tags[t] != .colon) continue;
            if (t + 1 > binding.rhs_last) return null;
            return .{ .first = t + 1, .last = binding.rhs_first - 1 };
        }
    }
    if (binding.origin == .alias) {
        const source = bindings.findAt(binding.origin.alias, binding.rhs_first) orelse return null;
        return declaredTypeRange(tree, tags, bindings, source, hops + 1);
    }
    return null;
}

/// `var arena = std.heap.ArenaAllocator.init(gpa);` — a value written
/// as a call on the proved library type.  Only `init` is read, because
/// the pinned `std.heap.ArenaAllocator.init` returns an
/// `ArenaAllocator`; a method that returns something else is not
/// guessed at.
fn builtByArenaConstructor(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    binding: *const local_bindings.Binding,
) bool {
    const call = binding.asCall() orelse return false;
    const start = binding.rhsFirstAfterTry(tags);
    if (tags[start] != .identifier) return false;
    // The callee is the token before the call's `(`; the path it was
    // written on is everything before the `.` in front of it.
    if (call.paren_token < start + 2) return false;
    const callee = call.paren_token - 1;
    if (tags[callee] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(callee), "init")) return false;
    if (tags[callee - 1] != .period) return false;
    return namesStdArena(cache, tree, start, callee - 2);
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    allocator_tok: Ast.TokenIndex,
    slice_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "std.heap.ArenaAllocator.free rewinds the arena only when the slice it is handed is that arena's most recent allocation; `{s}` is not, because an allocation with provably nonzero storage from the same arena is written after it, so this call releases nothing. Delete the call, or scope the arena so it ends with the allocation it owns",
        .{slice_name},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, allocator_tok),
        .end = Pos.fromTokenEnd(tree, allocator_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "arena-allocator-free-noop: a non-last slice from a proved std arena" {
    // The arena's cursor ends at `second`, so handing `first` back
    // cannot rewind it — nothing comes back.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn cleanup(arena: std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: the last slice is released, so the call is not a finding" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: the same arena reached through a field" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Ctx = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn cleanup(self: *Ctx) !void {
        \\        const first = try self.arena.allocator().alloc(u8, 8);
        \\        _ = try self.arena.allocator().alloc(u8, 8);
        \\        self.arena.allocator().free(first);
        \\    }
        \\};
        \\
    );
}

test "arena-allocator-free-noop: the same arena built by its own init" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn cleanup(gpa: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    defer arena.deinit();
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: a local alias of the library type answers the same" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Arena = std.heap.ArenaAllocator;
        \\fn cleanup(arena: Arena) !void {
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: a namespaced spelling of the library type answers the same" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const heap = std.heap;
        \\fn cleanup(arena: heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: a project ArenaAllocator whose free really releases is quiet" {
    try testing.expectNoFire(check,
        \\const ArenaAllocator = struct {
        \\    bytes: []u8 = &[_]u8{},
        \\    pub fn allocator(self: *ArenaAllocator) void {}
        \\    pub fn free(self: *ArenaAllocator, bytes: []u8) void {
        \\        self.bytes = &[_]u8{};
        \\        _ = bytes;
        \\    }
        \\};
        \\fn cleanup(arena: *ArenaAllocator, slice: []u8) void {
        \\    const first = slice;
        \\    _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: a receiver called arena proves nothing on its own" {
    // No declaration writes a type here, so the receiver's type is
    // unknown — silence, not a finding on the spelling.
    try testing.expectNoFire(check,
        \\fn cleanup(arena: *Cache, slice: []u8) void {
        \\    const first = slice;
        \\    _ = arena;
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: a branch between the allocation and the free is unknown" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: std.heap.ArenaAllocator, flag: bool) !void {
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    if (flag) _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: an intervening free can put the cursor back" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 8);
        \\    const second = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(second);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: a slice from another allocator is unknown" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: std.heap.ArenaAllocator, gpa: std.mem.Allocator) !void {
        \\    const first = try gpa.alloc(u8, 8);
        \\    _ = try arena.allocator().alloc(u8, 8);
        \\    arena.allocator().free(first);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: direct allocator.free does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(allocator: std.mem.Allocator) void {
        \\    allocator.free(slice);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: arena.deinit does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(self: *Self) void {
        \\    self.arena.deinit();
        \\}
        \\
    );
}

test "arena-allocator-free-noop: .allocator().alloc does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn alloc(self: *Self, n: usize) ![]u8 {
        \\    return self.arena.allocator().alloc(u8, n);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: non-arena receiver does not fire" {
    try testing.expectNoFire(check,
        \\const DevServer = struct {};
        \\fn cleanup(dev: *DevServer) void {
        \\    dev.allocator().free(dev.buffer);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: zero-length allocation does not prove cursor advance" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(u8, 0);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: zero-bit elements do not prove cursor advance" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(u0, 8);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: create empty struct does not prove cursor advance" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Empty = struct {};
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().create(Empty);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: dynamic allocation size is unknown" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn cleanup(arena: *std.heap.ArenaAllocator, n: usize) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(u8, n);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: known nonzero typed allocation advances cursor" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(u16, 2);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: known nonzero create advances cursor" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().create(u8);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: zero allocation after positive allocation cannot restore cursor" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(u8, 0);
        \\    arena.allocator().free(first);
        \\}
    );
}

test "arena-allocator-free-noop: cursor-changing allocator operations remain unknown" {
    inline for (.{ "resize", "remap", "realloc" }) |method| {
        const prefix = if (comptime std.mem.eql(u8, method, "realloc")) "try " else "";
        try testing.expectNoFire(check,
            \\const std = @import("std");
            \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
            \\    const first = try arena.allocator().alloc(u8, 4);
            \\    const second = try arena.allocator().alloc(u8, 4);
        ++ "    _ = " ++ prefix ++ "arena.allocator()." ++ method ++ "(second, 0);\n" ++
            \\    arena.allocator().free(first);
            \\}
        );
    }
}

test "arena-allocator-free-noop: unknown project element storage is not presumed positive" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Element = struct { bytes: [0]u8 };
        \\fn cleanup(arena: *std.heap.ArenaAllocator) !void {
        \\    const first = try arena.allocator().alloc(u8, 4);
        \\    _ = try arena.allocator().alloc(Element, 4);
        \\    arena.allocator().free(first);
        \\}
    );
}