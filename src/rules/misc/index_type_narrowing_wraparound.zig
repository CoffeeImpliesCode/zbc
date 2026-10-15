//! Report casts whose input does not have a proved destination range.
//!
//! The rule asks one question — can every value that reaches here be named by
//! the integer this conversion is written for? — about two surfaces.  One is a
//! collection LENGTH converted into a narrower integer.  The other is a value
//! narrowed on its way into a collection SUBSCRIPT, which is the same
//! conversion with the use spelled out instead of the `.len`.
//!
//! The indexed surface consumes the collection's ACTUAL capacity through the
//! guard that already mentions it, not through the subscript that comes later.
//! `if (index >= array.len) return null` reads `array.len` at the type the
//! collection really has, and it is that reading which decides the two
//! neighbouring bodies: a `[128]u8` turns the guard into a bound of 127,
//! which an `i8` names outright, and a `[129]u8` turns it into 128, which it
//! does not.  The subscript is deliberately NOT the evidence.  It runs after
//! the conversion, so a value that traps there says nothing about one that
//! already trapped in front of it — `raw = 256` into a three-element table
//! still traps in the `@intCast`, and a capacity small enough to be reached
//! never makes that conversion sound.
//! Type-domain widening does not depend on interval encoding. Known result
//! locations still require a sufficient source range; unresolved length
//! conversions retain their warning rather than borrowing the operand's type.
const std = @import("std");
const Ast = std.zig.Ast;
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const testing = @import("../../testing.zig");
const Problem = problem_mod.Problem;
const type_resolver_mod = @import("../../type_resolver.zig");
const Pos = problem_mod.Pos;

const R = "index-type-narrowing-wraparound";

/// How deep a subscript expression is read before it counts as unread.
const subscript_depth = 64;
/// How many alias hops are followed back from a subscript to a cast.
const alias_rounds = 8;
/// Room for the casts and locals ONE subscript names.  A subscript needing
/// more is not a shape a hand-written reader gets right, and dropping the
/// overflow only leaves a conversion unreported.
const subscript_room = 16;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .index_type_narrowing_wraparound)) return;
    var indexed = IndexedUses.init(gpa);
    defer indexed.deinit();
    try indexed.build(tree, cache);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (!isIntCast(tree, node)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        if (params.len != 1) continue;
        const length_cast = containsLength(tree, params[0], 0);
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        var uses: [2][]const IndexUse = .{ &.{}, &.{} };
        if (!length_cast) {
            // The value has to reach a subscript for this to be an index
            // conversion at all, and it reaches it either written in the
            // subscript itself or through the declaration the cast wrote.
            var found = false;
            if (indexed.direct.get(node)) |list| {
                if (list.items.len != 0) {
                    uses[0] = list.items;
                    found = true;
                }
            }
            if (indexed.declarer.get(node)) |name_token| {
                // What the cast produced is what the subscript reads, whatever
                // becomes of that slot afterwards.  A later write — on one
                // path or on every path — is a fact about the consumer, and
                // never about the conversion in front of it.
                if (indexed.bound.get(name_token)) |list| {
                    if (list.items.len != 0) {
                        uses[1] = list.items;
                        found = true;
                    }
                }
            }
            // A numeric conversion that never reaches a subscript is not an
            // index conversion, and a rule that answered from the
            // destination's width alone would report every one of them.
            if (!found) continue;
        }
        if (!isRuntimeUse(tree, declaration, token)) continue;
        var proved = false;
        var failed: ?IndexUse = null;
        if (destinationOf(cache, &indexed, node)) |destination| {
            if (try sourceOf(cache, tree, params[0])) |source| {
                proved = integerTypeFits(source, destination);
            }
            if (!proved) {
                // The range is what the ORACLE proves at the cast, taken whole.
                // A collection's capacity is not intersected into it: a
                // subscript that traps LATER cannot make the conversion in
                // front of it sound, and `raw = 256` into a three-element
                // table still traps in the conversion itself.
                const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, params[0], token, cache);
                proved = bounds.fitsInteger(destination.bits, destination.signed);
                if (!length_cast and !proved) {
                    for (uses) |slice| {
                        for (slice) |use| {
                            failed = use;
                            break;
                        }
                        if (failed != null) break;
                    }
                }
            }
        } else if (!length_cast) {
            // With no destination, an indexed value has no range to compare.
            // Length conversions retain their existing unproved-range warning.
            continue;
        }
        if (proved) continue;
        const message = if (length_cast)
            try gpa.dupe(u8, "the collection length was not proved to fit the destination integer; an out-of-range @intCast traps in Debug/ReleaseSafe and causes undefined behavior in unchecked builds, rather than defined wrapping; prove a bound or use a sufficient integer range")
        else
            try indexMessage(gpa, failed.?);
        errdefer gpa.free(message);
        try problems.append(gpa, .{
            .rule_id = R,
            .severity = .warning,
            .start = try Pos.fromTokenStart(tree, token),
            .end = try Pos.fromTokenEnd(tree, tree.lastToken(node)),
            .message = message,
        });
    }
}

/// True when the use at `token` runs at runtime: it sits inside
/// `declaration`'s body but outside any `comptime { … }` block (or
/// `comptime label: { … }` block) and outside the expression a bare
/// `comptime` keyword governs.  The compiler checks what it evaluates
/// itself, so a conversion that can only ever run there is not a
/// runtime hazard this rule reports.  A use this cannot place is a
/// runtime use: an unreadable seam declines into the check, never out
/// of it.
fn isRuntimeUse(tree: *const Ast, declaration: Ast.Node.Index, token: Ast.TokenIndex) bool {
    const body = tokens.bodyOf(tree, declaration) orelse return true;
    const first = tree.firstToken(body);
    if (token < first) return true;
    const tags = tree.tokens.items(.tag);
    var stack: [64]Ast.TokenIndex = undefined;
    var depth: usize = 0;
    var t = first;
    while (t <= token) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (depth < stack.len) stack[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
            },
            else => {},
        }
    }
    var i = depth;
    while (i > 0) {
        i -= 1;
        if (i >= stack.len) continue;
        const brace = stack[i];
        if (brace == 0) continue;
        if (tags[brace - 1] == .keyword_comptime) return false;
        if (brace >= 3 and tags[brace - 3] == .keyword_comptime and
            tags[brace - 2] == .identifier and tags[brace - 1] == .colon) return false;
    }
    return !statementStartsWithComptime(tags, first, token);
}

/// True when the statement owning `token` is written under a bare
/// `comptime` keyword (`comptime assert(x[i] == 0);`), or `token` sits
/// inside the parenthesised call such a keyword governs.  Only the
/// expression the keyword opens counts: once a group it did not open
/// closes, the rest of the statement runs at runtime.
fn statementStartsWithComptime(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, token: Ast.TokenIndex) bool {
    var start = first;
    var t = token;
    while (t > first) : (t -= 1) {
        switch (tags[t]) {
            .semicolon, .l_brace, .r_brace => {
                start = t + 1;
                break;
            },
            else => {},
        }
    }
    var c: ?Ast.TokenIndex = null;
    t = start;
    while (t < token) : (t += 1) {
        if (tags[t] == .keyword_comptime) {
            c = t;
            break;
        }
    }
    const comptime_tok = c orelse return false;
    var depth: i32 = 0;
    t = comptime_tok + 1;
    while (t < token) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => {
                depth -= 1;
                if (depth < 0) return false;
            },
            else => {},
        }
    }
    return true;
}

fn indexMessage(gpa: std.mem.Allocator, reported: IndexUse) ![]u8 {
    // The capacity names the collection the value was proved to subscript; it
    // is context for the finding and never a term in the verdict, which is
    // settled by the range the oracle proved AT the cast.
    var owned: ?[]u8 = null;
    defer if (owned) |text| gpa.free(text);
    const sized: []const u8 = if (reported.capacity) |count| blk: {
        const text = try std.fmt.allocPrint(gpa, "before indexing a collection of {d} elements", .{count});
        owned = text;
        break :blk text;
    } else "before indexing a collection of runtime length";
    return std.fmt.allocPrint(gpa, "the value was not proved to fit the destination integer {s}; an out-of-range @intCast traps in Debug/ReleaseSafe and causes undefined behavior in unchecked builds, rather than defined wrapping; prove a bound or use a sufficient integer range", .{sized});
}

fn isIntCast(tree: *const Ast, node: Ast.Node.Index) bool {
    return std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intCast");
}

/// Compare type domains directly: the interval oracle deliberately cannot
/// encode u128, but every u128 still fits u128 or a wider signed integer.
fn integerTypeFits(source: type_resolver_mod.TypeResolver.IntInfo, destination: type_resolver_mod.TypeResolver.IntInfo) bool {
    if (source.bits == 0) return true;
    if (source.signed == destination.signed) return source.bits <= destination.bits;
    return !source.signed and destination.signed and source.bits < destination.bits;
}

/// Only actual arrays and slice headers have a builtin usize length. A field
/// named `len` on a user container, or an opaque receiver, has no such domain.
fn sourceOf(cache: *file_cache_mod.FileCache, tree: *const Ast, original: Ast.Node.Index) anyerror!?type_resolver_mod.TypeResolver.IntInfo {
    if (cache.intInfoOf(original)) |info| return info;
    var node = original;
    while (tree.nodeTag(node) == .grouped_expression) node = tree.nodeData(node).node_and_token[0];
    if (tree.nodeTag(node) != .field_access) return null;
    const receiver, const field = tree.nodeData(node).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(field), "len")) return null;
    const resolver = cache.zls orelse return null;
    var actual = (try resolver.resolutionFrame().typeOfNode(receiver)) orelse return null;
    if (resolver.pointerSize(actual) == .one) {
        actual = (try resolver.normalizedType(resolver.childType(actual) orelse return null)) orelse return null;
    }
    if (resolver.typeTag(actual) == .array or resolver.pointerSize(actual) == .slice)
        return .{ .bits = @bitSizeOf(usize), .signed = false };
    return null;
}

fn containsLength(tree: *const Ast, node: Ast.Node.Index, depth: u8) bool {
    if (depth == 64) return false;
    if (tree.nodeTag(node) == .field_access) {
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeData(node).node_and_token[1]), "len")) return true;
    }
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| {
        if (containsLength(tree, child, depth + 1)) return true;
    }
    return false;
}

/// One collection a narrowed value is used to subscript.
const IndexUse = struct {
    /// Compile-time element count of the indexed collection, or null when it
    /// is a runtime-sized slice.  A null is not "no capacity": it is the
    /// admission that only the oracle's own facts can bound the subscript.
    capacity: ?u64,
};

/// One span of source that coerces what is written inside it to a type the
/// source spells out: the initializer of an annotated declaration, or the
/// value of a `return`.  A null `type` is a span that coerces to nothing,
/// which STOPS the search rather than letting the span around it answer for
/// a cast it does not coerce.
const Coercion = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    type: ?Ast.Node.Index,
    /// Set on a fn declaration, which coerces nothing by itself: it is
    /// recorded so the `return`s inside it can find what that fn returns.
    returns: ?Ast.Node.Index,
};

/// The span an annotated declaration coerces its INITIALIZER to.  The span
/// is the initializer and not the whole declaration, because the annotation
/// says nothing about the align expression written beside it.
fn varDeclType(tree: *const Ast, node: Ast.Node.Index) Coercion {
    var span: Coercion = .{
        .first = tree.firstToken(node),
        .last = tree.lastToken(node),
        .type = null,
        .returns = null,
    };
    const declaration = tree.fullVarDecl(node) orelse return span;
    const initializer = declaration.ast.init_node.unwrap() orelse return span;
    span.first = tree.firstToken(initializer);
    span.last = tree.lastToken(initializer);
    span.type = declaration.ast.type_node.unwrap();
    return span;
}

/// The span of a fn, coercing nothing itself and carrying the type that fn
/// returns for the `return`s written inside it.
fn fnDeclaration(tree: *const Ast, node: Ast.Node.Index) Coercion {
    var buffer: [1]Ast.Node.Index = undefined;
    const prototype = tokens.fnProto(tree, &buffer, node);
    return .{
        .first = tree.firstToken(node),
        .last = tree.lastToken(node),
        .type = null,
        .returns = if (prototype) |readable| readable.ast.return_type.unwrap() else null,
    };
}

/// The span of a `return`, coercing to the type the fn around it returns.
fn returnCoercion(tree: *const Ast, node: Ast.Node.Index, contexts: []const Coercion) Coercion {
    var span: Coercion = .{
        .first = tree.firstToken(node),
        .last = tree.lastToken(node),
        .type = null,
        .returns = null,
    };
    var index = contexts.len;
    while (index > 0) {
        index -= 1;
        const enclosing = contexts[index];
        if (enclosing.returns == null) continue;
        if (span.first < enclosing.first or span.last > enclosing.last) continue;
        span.type = enclosing.returns;
        break;
    }
    return span;
}

/// The type `node` is written to be coerced into, or null when the span that
/// coerces it spells no type.  Contexts are in the order the walk met them
/// and their spans nest, so the innermost one is the last that still
/// contains the node.
fn innermostType(tree: *const Ast, node: Ast.Node.Index, contexts: []const Coercion) ?Ast.Node.Index {
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    var index = contexts.len;
    while (index > 0) {
        index -= 1;
        const span = contexts[index];
        if (first < span.first or last > span.last) continue;
        return span.type;
    }
    return null;
}

/// True when `node` is written inside one of `spans` — a subscript decides
/// the type of everything inside it, and a cast read by a collection index
/// is coerced by that index rather than by anything written around it.
fn insideAny(tree: *const Ast, node: Ast.Node.Index, spans: []const Coercion) bool {
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    for (spans) |span| {
        if (first < span.first or last > span.last) continue;
        return true;
    }
    return false;
}

/// The integer type `node` is converted INTO, or null when nothing written
/// around it says which.  Argument position is the type engine's own
/// question; everywhere else the type is spelled out beside the cast, and
/// that spelling is the answer.
fn destinationOf(
    cache: *file_cache_mod.FileCache,
    indexed: *const IndexedUses,
    node: Ast.Node.Index,
) ?type_resolver_mod.TypeResolver.IntInfo {
    if (cache.coercedIntInfoOf(node)) |info| return info;
    if (indexed.coerced.get(node)) |type_node| {
        return cache.intInfoOf(type_node) orelse cache.optionalPayloadIntInfoOf(type_node);
    }
    // `target = @intCast(x)`: the cast takes the type of what it is stored
    // into, and for an optional target that is the payload's integer.
    const target = indexed.assigned.get(node) orelse return null;
    return cache.intInfoOf(target) orelse cache.optionalPayloadIntInfoOf(target);
}

/// Which `@intCast`s in this file reach a collection subscript, and which
/// collections they reach.
///
/// ONE walk builds this and every later question is a hash probe, so a file
/// with many conversions is not rescanned once per conversion.  A value is
/// followed by the name token that NAMES its declaration and not by the
/// spelling, which is what keeps a shadowing local and the declaration it
/// shadows two different values.
const IndexedUses = struct {
    gpa: std.mem.Allocator,
    /// A cast written inside a subscript: what that subscript indexes.
    direct: std.AutoHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(IndexUse)),
    /// A local declaration whose value reaches a subscript.
    bound: std.AutoHashMapUnmanaged(Ast.TokenIndex, std.ArrayListUnmanaged(IndexUse)),
    /// The declaration a cast initializes, keyed by the cast.
    declarer: std.AutoHashMapUnmanaged(Ast.Node.Index, Ast.TokenIndex),
    /// The bindings of each fn whose body was walked, keyed by the fn.
    bindings: std.AutoHashMapUnmanaged(Ast.Node.Index, *const local_bindings.LocalBindings),
    /// The type a cast is COERCED into where a type is spelled out: the
    /// annotation of the declaration whose initializer it is, or the return
    /// type of the fn whose `return` it is.  Argument position is the type
    /// engine's own `coercedIntInfoOf` — a parameter's type is written
    /// beside the call, not at the cast.
    coerced: std.AutoHashMapUnmanaged(Ast.Node.Index, Ast.Node.Index),
    /// The target of a plain assignment whose whole right-hand side is the
    /// cast, keyed by the cast.
    assigned: std.AutoHashMapUnmanaged(Ast.Node.Index, Ast.Node.Index),

    fn init(gpa: std.mem.Allocator) IndexedUses {
        return .{
            .gpa = gpa,
            .direct = .empty,
            .bound = .empty,
            .declarer = .empty,
            .bindings = .empty,
            .coerced = .empty,
            .assigned = .empty,
        };
    }

    fn deinit(self: *IndexedUses) void {
        var direct = self.direct.valueIterator();
        while (direct.next()) |list| list.deinit(self.gpa);
        var bound = self.bound.valueIterator();
        while (bound.next()) |list| list.deinit(self.gpa);
        self.direct.deinit(self.gpa);
        self.bound.deinit(self.gpa);
        self.declarer.deinit(self.gpa);
        self.bindings.deinit(self.gpa);
        self.coerced.deinit(self.gpa);
        self.assigned.deinit(self.gpa);
    }

    fn build(self: *IndexedUses, tree: *const Ast, cache: *file_cache_mod.FileCache) !void {
        // ONE walk collects every span that coerces, and the casts that will
        // be asked about them.  The question is settled after the walk, not
        // during it: the parser writes a parent node before the expressions
        // it encloses, so the `return` a cast sits in is only a known span
        // once the walk has been past that cast.
        var contexts: std.ArrayListUnmanaged(Coercion) = .empty;
        defer contexts.deinit(self.gpa);
        var subscripts: std.ArrayListUnmanaged(Coercion) = .empty;
        defer subscripts.deinit(self.gpa);
        var casts: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        defer casts.deinit(self.gpa);
        for (tree.nodes.items(.tag), 0..) |tag, index| {
            const node: Ast.Node.Index = @enumFromInt(index);
            switch (tag) {
                .array_access => {
                    try subscripts.append(self.gpa, .{
                        .first = tree.firstToken(node),
                        .last = tree.lastToken(node),
                        .type = null,
                        .returns = null,
                    });
                    try self.readAccess(tree, cache, node);
                },
                .global_var_decl, .local_var_decl, .aligned_var_decl, .simple_var_decl => {
                    try contexts.append(self.gpa, varDeclType(tree, node));
                    try self.readDecl(tree, node);
                },
                .fn_decl => try contexts.append(self.gpa, fnDeclaration(tree, node)),
                .@"return" => try contexts.append(self.gpa, returnCoercion(tree, node, contexts.items)),
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (isIntCast(tree, node)) try casts.append(self.gpa, node);
                },
                .assign => {
                    const target, const value = tree.nodeData(node).node_and_node;
                    if (isIntCast(tree, value)) try self.assigned.put(self.gpa, value, target);
                },
                else => {},
            }
        }
        for (casts.items) |cast| {
            // A subscript coerces what it reads to the index type it
            // computes, and that is not a type this tier resolves, so
            // nothing written around the cast answers for it.
            if (insideAny(tree, cast, subscripts.items)) continue;
            if (innermostType(tree, cast, contexts.items)) |type_node| {
                try self.coerced.put(self.gpa, cast, type_node);
            }
        }
        try self.expandAliases();
    }

    fn readDecl(self: *IndexedUses, tree: *const Ast, node: Ast.Node.Index) !void {
        const declaration = tree.fullVarDecl(node) orelse return;
        const initializer = declaration.ast.init_node.unwrap() orelse return;
        if (!isIntCast(tree, initializer)) return;
        const name_token = declaration.ast.mut_token + 1;
        // A destructuring `const .{ a, b } = @intCast(x)` has no single token
        // to key on, and a name this tier cannot settle is not a binding.
        if (tree.tokenTag(name_token) != .identifier) return;
        try self.declarer.put(self.gpa, initializer, name_token);
    }

    fn readAccess(self: *IndexedUses, tree: *const Ast, cache: *file_cache_mod.FileCache, access: Ast.Node.Index) !void {
        const operands = tree.nodeData(access).node_and_node;
        var found: Found = .{};
        found.read(tree, operands[1], 0);
        // A subscript naming neither a local nor a cast connects nothing, and
        // the collection's type is not worth resolving for it.
        if (found.casts == 0 and found.names == 0) return;
        const use: IndexUse = .{ .capacity = cache.fixedArrayLenOf(operands[0]) };
        for (found.cast_nodes[0..found.casts]) |cast| _ = try record(self.gpa, Ast.Node.Index, &self.direct, cast, use);
        if (found.names != 0) {
            const declaration = tokens.enclosingFnDecl(tree, tree.nodeMainToken(access)) orelse return;
            const table = (try self.bindingsOf(tree, cache, declaration)) orelse return;
            for (found.name_tokens[0..found.names]) |name_token| {
                const binding = table.findAt(tree.tokenSlice(name_token), name_token) orelse continue;
                _ = try record(self.gpa, Ast.TokenIndex, &self.bound, binding.name_token, use);
            }
        }
    }

    /// The casts and the locals ONE subscript names.
    const Found = struct {
        cast_nodes: [subscript_room]Ast.Node.Index = undefined,
        casts: usize = 0,
        name_tokens: [subscript_room]Ast.TokenIndex = undefined,
        names: usize = 0,

        fn read(self: *Found, tree: *const Ast, node: Ast.Node.Index, depth: u8) void {
            if (depth == subscript_depth) return;
            switch (tree.nodeTag(node)) {
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (isIntCast(tree, node) and self.casts < subscript_room) {
                        self.cast_nodes[self.casts] = node;
                        self.casts += 1;
                    }
                },
                .identifier => {
                    if (self.names < subscript_room) {
                        self.name_tokens[self.names] = tree.nodeMainToken(node);
                        self.names += 1;
                    }
                },
                else => {},
            }
            var children = @import("type_engine").AstIterator.init(tree, node);
            while (children.next(tree)) |child| self.read(tree, child, depth + 1);
        }
    };

    /// A subscript may name an alias rather than the value itself, and what
    /// the alias names is what the cast produced.  Following those hops is
    /// what connects `const at = narrow; return array[at];` to the cast that
    /// made `narrow`.
    fn expandAliases(self: *IndexedUses) !void {
        var rounds: u8 = 0;
        while (rounds < alias_rounds) : (rounds += 1) {
            var changed = false;
            var by_fn = self.bindings.iterator();
            while (by_fn.next()) |entry| {
                const table = entry.value_ptr.*;
                for (table.items) |binding| {
                    const source = switch (binding.origin) {
                        .alias => |name| name,
                        else => continue,
                    };
                    var uses: [subscript_room]IndexUse = undefined;
                    var used: usize = 0;
                    const reached = self.bound.get(binding.name_token) orelse continue;
                    for (reached.items) |use| {
                        if (used == uses.len) break;
                        uses[used] = use;
                        used += 1;
                    }
                    if (used == 0) continue;
                    const target = table.findAt(source, binding.name_token) orelse continue;
                    for (uses[0..used]) |use| {
                        if (try record(self.gpa, Ast.TokenIndex, &self.bound, target.name_token, use)) changed = true;
                    }
                }
            }
            if (!changed) return;
        }
    }

    fn bindingsOf(
        self: *IndexedUses,
        tree: *const Ast,
        cache: *file_cache_mod.FileCache,
        declaration: Ast.Node.Index,
    ) !?*const local_bindings.LocalBindings {
        const body = tokens.bodyOf(tree, declaration) orelse return null;
        if (self.bindings.get(declaration)) |built| return built;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
        const built = try cache.localBindings(proto, body);
        // Published only once the build has succeeded, and only into a slot
        // this call created.  A slot reserved before the build would hand
        // the next caller the `undefined` value an entry's first write
        // leaves behind — a `*const LocalBindings` no build ever made.
        try self.bindings.put(self.gpa, declaration, built);
        return built;
    }
};

/// Record that `key` feeds `use`, once.  True when this added it.
fn record(
    gpa: std.mem.Allocator,
    comptime Key: type,
    map: *std.AutoHashMapUnmanaged(Key, std.ArrayListUnmanaged(IndexUse)),
    key: Key,
    use: IndexUse,
) !bool {
    const gop = try map.getOrPut(gpa, key);
    if (!gop.found_existing) gop.value_ptr.* = .empty;
    for (gop.value_ptr.items) |seen| {
        if (seen.capacity == use.capacity) return false;
    }
    try gop.value_ptr.append(gpa, use);
    return true;
}

test "index-type-narrowing-wraparound: range proof accepts a fixed array" {
    try testing.expectNoFireTyped(check,
        \\fn end(array: *const [128]u8) i16 {
        \\    var index: i16 = @intCast(array.len);
        \\    index -= 1;
        \\    return index;
        \\}
    );
}

test "index-type-narrowing-wraparound: range proof ignores maximum spelling" {
    try testing.expectFiresTyped(check, R,
        \\const max_i16 = 70000;
        \\fn end(array: []const u8) i16 {
        \\    var index: i16 = @intCast(@min(array.len, max_i16));
        \\    index -= 1;
        \\    return index;
        \\}
    );
}

test "index-type-narrowing-wraparound: the destination boundary on a fixed array length is exact" {
    // Three lengths, one `i16`, and nothing else different between them.
    // 32767 is the last value an `i16` names, so the middle body is the only
    // one of the three where the conversion cannot trap — and what decides it
    // there is the LENGTH, not the collection's name, not the spelling, and
    // not the width the source type happens to have: `array.len` is a `usize`
    // in all three, which on its own would silence every one of them.
    try testing.expectFiresTyped(check, R,
        \\pub fn end(array: *const [70000]u8) i16 {
        \\    return @intCast(array.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn end(array: *const [32767]u8) i16 {
        \\    return @intCast(array.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn end(array: *const [32768]u8) i16 {
        \\    return @intCast(array.len);
        \\}
    );
}

// ── The boundary the compiler keeps ─────────────────────────────────────
//
// The number above is a boundary the COMPILER also keeps: `[32767]u8` is
// exactly as long as an `i16` can count, so the conversion on the safe side
// is not merely unproved — it is legal, and it produces the number of
// elements the array really has.  One element more is refused by the
// language itself, which is why the unsafe side of the pair is a compiler
// rejection rather than a fixture here that would not build at all.

test "index-type-narrowing-wraparound: a length the destination admits is the count the array holds" {
    const Table = struct {
        fn end(array: *const [32767]u8) i16 {
            return @intCast(array.len);
        }
    };
    // Only the COUNT is read, so the elements need no values; `const` is what
    // says the binding is never written, which is the whole of what this
    // conversion is about.
    const storage: [32767]u8 = undefined;
    try std.testing.expectEqual(@as(i16, 32767), Table.end(&storage));
}

test "index-type-narrowing-wraparound: signed index spelling is not a narrowing conversion" {
    try testing.expectNoFireTyped(check,
        \\fn first(array: []const u8) u8 {
        \\    var index: i16 = 0;
        \\    index += 1;
        \\    return array[@intCast(index)];
        \\}
    );
}

test "index-type-narrowing-wraparound: unsigned destinations also require bounds" {
    try testing.expectFiresTyped(check, R,
        \\fn size(array: []const u8) u16 { return @intCast(array.len); }
    );
    try testing.expectNoFireTyped(check,
        \\fn size(array: []const u8) u16 {
        \\    if (array.len > 65535) return 0;
        \\    return @intCast(array.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: trusted clipping uses the actual destination maximum" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn size(array: []const u8) i16 { return @intCast(@min(array.len, std.math.maxInt(i16))); }
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn size(array: []const u8) i16 { return @intCast(@min(array.len, std.math.maxInt(i32))); }
    );
}

// ── Effects between the guard and the cast ────────────────────────────────
//
// A bound proved by a guard is a fact about storage.  What may end it is an
// effect that can WRITE that storage, not any statement at all: a handler
// that reads a slice is handed a copy of the header and cannot touch the
// caller's frame slot.

test "index-type-narrowing-wraparound: a catch handler that only reads keeps the guard" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn widen(text: []const u8) !u32 {
        \\    if (text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    const total = std.math.add(usize, text.len, 3) catch return error.Capacity;
        \\    _ = total;
        \\    const sentinel: u32 = @intCast(text.len);
        \\    return sentinel;
        \\}
    );
}

test "index-type-narrowing-wraparound: an orelse handler that only reads keeps the guard" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn widen(text: []const u8) !u32 {
        \\    if (text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    const total = std.math.add(usize, text.len, 3) orelse return error.Capacity;
        \\    _ = total;
        \\    const sentinel: u32 = @intCast(text.len);
        \\    return sentinel;
        \\}
    );
}

test "index-type-narrowing-wraparound: a callee handed the bytes cannot change the caller's length slot" {
    // `fill` receives a `[]u8` header pointing at the same bytes, but the
    // caller's own `text` frame slot — the one `text.len` reads — is not
    // reachable from that header.  Charging a slice argument with writing the
    // length is what made the guard disappear here.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn fill(buffer: []u8) void { for (buffer, 0..) |*byte, i| byte.* = @intCast(i); }
        \\fn widen(text: []const u8) !u32 {
        \\    if (text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    const total = std.math.add(usize, text.len, 3) catch {
        \\        fill(@constCast(text));
        \\        return error.Capacity;
        \\    };
        \\    _ = total;
        \\    const sentinel: u32 = @intCast(text.len);
        \\    return sentinel;
        \\}
    );
}

test "index-type-narrowing-wraparound: a handler that writes the same path still drops the guard" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Holder = struct { text: []const u8 };
        \\fn widen(holder: *Holder) !u32 {
        \\    if (holder.text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    const total = std.math.add(usize, holder.text.len, 3) catch {
        \\        holder.text = "replaced";
        \\        return error.Capacity;
        \\    };
        \\    _ = total;
        \\    const sentinel: u32 = @intCast(holder.text.len);
        \\    return sentinel;
        \\}
    );
}

test "index-type-narrowing-wraparound: an errdefer that only reads keeps the guard" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn widen(text: []const u8, arena: *std.ArrayList(u8)) !u32 {
        \\    if (text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    errdefer arena.deinit(std.heap.page_allocator);
        \\    try arena.append(std.heap.page_allocator, 'a');
        \\    const sentinel: u32 = @intCast(text.len);
        \\    return sentinel;
        \\}
    );
}

test "index-type-narrowing-wraparound: an assignment leaves an unrelated path's guard alone" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Holder = struct { text: []const u8, count: usize = 0 };
        \\fn widen(holder: *Holder) !u32 {
        \\    if (holder.text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    holder.count = describe(holder.count);
        \\    const sentinel: u32 = @intCast(holder.text.len);
        \\    return sentinel;
        \\}
        \\fn describe(value: usize) usize { return value + 1; }
    );
}

test "index-type-narrowing-wraparound: an assignment through an unlocatable target still drops the guard" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Holder = struct { text: []const u8, count: *usize };
        \\fn widen(holder: *Holder) !u32 {
        \\    if (holder.text.len > std.math.maxInt(u32)) return error.InputTooLarge;
        \\    holder.count.* = 1;
        \\    const sentinel: u32 = @intCast(holder.text.len);
        \\    return sentinel;
        \\}
    );
}

test "index-type-narrowing-wraparound: a std capacity call keeps a copied length guard" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const State = struct {
        \\    paths: std.ArrayListUnmanaged([]const u8) = .empty,
        \\    fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) !u32 {
        \\        const length = self.paths.items.len;
        \\        if (length > std.math.maxInt(u32)) return error.Overflow;
        \\        try self.paths.ensureUnusedCapacity(gpa, 1);
        \\        const id: u32 = @intCast(length);
        \\        self.paths.appendAssumeCapacity(path);
        \\        return id;
        \\    }
        \\};
    );
}

test "index-type-narrowing-wraparound: a std append still drops the length guard" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const State = struct {
        \\    paths: std.ArrayListUnmanaged([]const u8) = .empty,
        \\    fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) !u32 {
        \\        if (self.paths.items.len > std.math.maxInt(u32)) return error.Overflow;
        \\        try self.paths.append(gpa, path);
        \\        const id: u32 = @intCast(self.paths.items.len);
        \\        return id;
        \\    }
        \\};
    );
}

test "index-type-narrowing-wraparound: a project method named like a capacity call still drops the length guard" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Paths = struct {
        \\    items: []const u8 = &.{},
        \\    fn ensureUnusedCapacity(self: *Paths, count: usize) void {
        \\        self.items = self.items.ptr[0 .. self.items.len + count];
        \\    }
        \\};
        \\const State = struct {
        \\    paths: Paths = .{},
        \\    fn intern(self: *State) u32 {
        \\        if (self.paths.items.len > std.math.maxInt(u32)) return 0;
        \\        self.paths.ensureUnusedCapacity(1);
        \\        const id: u32 = @intCast(self.paths.items.len);
        \\        return id;
        \\    }
        \\};
    );
}

test "index-type-narrowing-wraparound: std sibling capacity calls keep a copied length guard" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const State = struct {
        \\    path_text: std.ArrayList([]const u8) = .empty,
        \\    paths: std.StringHashMapUnmanaged(u32) = .empty,
        \\    fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) !u32 {
        \\        const length = self.path_text.items.len;
        \\        if (length > std.math.maxInt(u32)) return error.Budget;
        \\        try self.path_text.ensureUnusedCapacity(gpa, 1);
        \\        try self.paths.ensureUnusedCapacity(gpa, 1);
        \\        const id: u32 = @intCast(length);
        \\        self.path_text.appendAssumeCapacity(path);
        \\        self.paths.putAssumeCapacity(path, id);
        \\        return id;
        \\    }
        \\};
    );
}

test "index-type-narrowing-wraparound: a project method on a sibling field still drops the length guard" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Sibling = struct {
        \\    n: usize = 0,
        \\    fn reserve(self: *Sibling, count: usize) void {
        \\        self.n += count;
        \\    }
        \\};
        \\const State = struct {
        \\    path_text: std.ArrayList([]const u8) = .empty,
        \\    sibling: Sibling = .{},
        \\    fn intern(self: *State, gpa: std.mem.Allocator) !u32 {
        \\        if (self.path_text.items.len > std.math.maxInt(u32)) return error.Budget;
        \\        self.sibling.reserve(1);
        \\        const id: u32 = @intCast(self.path_text.items.len);
        \\        _ = gpa;
        \\        return id;
        \\    }
        \\};
    );
}

test "index-type-narrowing-wraparound: a std append on the guarded field itself still drops the length guard" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const State = struct {
        \\    path_text: std.ArrayList([]const u8) = .empty,
        \\    paths: std.StringHashMapUnmanaged(u32) = .empty,
        \\    fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) !u32 {
        \\        if (self.path_text.items.len > std.math.maxInt(u32)) return error.Budget;
        \\        try self.paths.ensureUnusedCapacity(gpa, 1);
        \\        try self.path_text.append(gpa, path);
        \\        const id: u32 = @intCast(self.path_text.items.len);
        \\        return id;
        \\    }
        \\};
    );
}

// ── The destination a conversion is written into ──────────────────────────
//
// `@intCast(x)` has no type of its own: Zig gives it the type of the context
// it appears in.  In argument position that context is the parameter the
// argument is passed as, and a checker that reads only the cast's own type
// has no destination to check against and reports a conversion that cannot
// trap.

test "index-type-narrowing-wraparound: a cast in argument position is checked against the parameter's type" {
    try testing.expectNoFireTyped(check,
        \\const contract = struct {
        \\    fn mix(checksum: *u64, word: u64) void {
        \\        checksum.* +%= word;
        \\    }
        \\};
        \\const Document = struct { tape: []const u8 };
        \\fn checksum(document: *const Document) u64 {
        \\    var sum: u64 = 0;
        \\    contract.mix(&sum, @intCast(document.tape.len));
        \\    return sum;
        \\}
    );
}

test "index-type-narrowing-wraparound: a parameter narrower than the source still reports" {
    try testing.expectFiresTyped(check, R,
        \\const contract = struct {
        \\    fn mix(checksum: *u64, word: u32) void {
        \\        checksum.* +%= word;
        \\    }
        \\};
        \\const Document = struct { tape: []const u8 };
        \\fn checksum(document: *const Document) u64 {
        \\    var sum: u64 = 0;
        \\    contract.mix(&sum, @intCast(document.tape.len));
        \\    return sum;
        \\}
    );
}

test "index-type-narrowing-wraparound: a cast stored into a wide field is not a narrowing" {
    try testing.expectNoFireTyped(check,
        \\const Info = struct { extent: u64 = 0 };
        \\fn note(info: *Info, items: []const u32) void {
        \\    info.extent = @intCast(items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: a cast stored into an optional wide field is not a narrowing" {
    try testing.expectNoFireTyped(check,
        \\const Info = struct { extent: ?u64 = null };
        \\fn note(info: *Info, items: []const u32) void {
        \\    info.extent = @intCast(items.len);
        \\}
        \\fn local(items: []const u32) ?u64 {
        \\    const extent: ?u64 = @intCast(items.len);
        \\    return extent;
        \\}
    );
}

test "index-type-narrowing-wraparound: a cast stored into a narrow field still reports" {
    try testing.expectFiresTyped(check, R,
        \\const Info = struct { extent: u8 = 0 };
        \\fn note(info: *Info, items: []const u32) void {
        \\    info.extent = @intCast(items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: a cast stored into an optional narrow field still reports" {
    try testing.expectFiresTyped(check, R,
        \\const Info = struct { extent: ?u8 = null };
        \\fn note(info: *Info, items: []const u32) void {
        \\    info.extent = @intCast(items.len);
        \\}
    );
}

// ── A table validated at compile time ─────────────────────────────────────
//
// `comptime { for (TABLE) |e| if (LIMIT < e.f.len) @compileError(..); }` is
// how a generated table is validated, and the branch that would reject a
// violating element is one the compiler took and did not take.  Nothing
// else in the file says how wide the elements are: the table is a
// fixed-size array of a slice field, whose length is a value rather than a
// type, so without the audit the only honest answer is "unknown".

test "index-type-narrowing-wraparound: a compile-time audit bounds the element it drew" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Entry = struct { name: []const u8, value: []const u8 };
        \\const table = struct {
        \\    const entries = [_]Entry{
        \\        .{ .name = "amp", .value = "&" },
        \\        .{ .name = "lt", .value = "<" },
        \\    };
        \\};
        \\const width = 16;
        \\comptime {
        \\    for (table.entries) |entry| {
        \\        if (width < entry.value.len) @compileError("entry does not fit");
        \\    }
        \\}
        \\fn lookup(name: []const u8) u8 {
        \\    var index: usize = 0;
        \\    while (index < table.entries.len) : (index += 1) {
        \\        const entry = table.entries[index];
        \\        if (!std.mem.eql(u8, name, entry.name)) continue;
        \\        const len: u8 = @intCast(entry.value.len);
        \\        return len;
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-type-narrowing-wraparound: an unaudited element is still unbounded" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Entry = struct { name: []const u8, value: []const u8 };
        \\const table = struct {
        \\    const entries = [_]Entry{
        \\        .{ .name = "amp", .value = "&" },
        \\        .{ .name = "lt", .value = "<" },
        \\    };
        \\};
        \\fn lookup(name: []const u8) u8 {
        \\    var index: usize = 0;
        \\    while (index < table.entries.len) : (index += 1) {
        \\        const entry = table.entries[index];
        \\        if (!std.mem.eql(u8, name, entry.name)) continue;
        \\        const len: u8 = @intCast(entry.value.len);
        \\        return len;
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-type-narrowing-wraparound: an audit that permits more than the destination holds still reports" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Entry = struct { name: []const u8, value: []const u8 };
        \\const table = struct {
        \\    const entries = [_]Entry{
        \\        .{ .name = "amp", .value = "&" },
        \\        .{ .name = "lt", .value = "<" },
        \\    };
        \\};
        \\const width = 400;
        \\comptime {
        \\    for (table.entries) |entry| {
        \\        if (width < entry.value.len) @compileError("entry does not fit");
        \\    }
        \\}
        \\fn lookup(name: []const u8) u8 {
        \\    var index: usize = 0;
        \\    while (index < table.entries.len) : (index += 1) {
        \\        const entry = table.entries[index];
        \\        if (!std.mem.eql(u8, name, entry.name)) continue;
        \\        const len: u8 = @intCast(entry.value.len);
        \\        return len;
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-type-narrowing-wraparound: a guard the audit can step over is not an audit" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Entry = struct { name: []const u8, value: []const u8 };
        \\const table = struct {
        \\    const entries = [_]Entry{
        \\        .{ .name = "amp", .value = "&" },
        \\        .{ .name = "lt", .value = "<" },
        \\    };
        \\};
        \\const width = 16;
        \\comptime {
        \\    for (table.entries) |entry| {
        \\        if (entry.value.len == 0) break;
        \\        if (width < entry.value.len) @compileError("entry does not fit");
        \\    }
        \\}
        \\fn lookup(name: []const u8) u8 {
        \\    var index: usize = 0;
        \\    while (index < table.entries.len) : (index += 1) {
        \\        const entry = table.entries[index];
        \\        if (!std.mem.eql(u8, name, entry.name)) continue;
        \\        const len: u8 = @intCast(entry.value.len);
        \\        return len;
        \\    }
        \\    return 0;
        \\}
    );
}

// ── Contracts across a call ───────────────────────────────────────────────
//
// A bound lives where it is written.  A callee cannot see the ceiling its
// caller set on the storage it was handed, and a caller cannot see the
// ceiling the callee enforced on the way out.  Both are the same fact seen
// from the two ends of one call, so each is read from the call and restated
// in the name the other side writes.

test "index-type-narrowing-wraparound: a ceiling the caller writes on the receiver reaches the callee" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    fn store(self: *Builder, bytes: []const u8) u32 {
        \\        if (bytes.len > self.max_text_bytes) return 0;
        \\        const len: u32 = @intCast(bytes.len);
        \\        return len;
        \\    }
        \\};
        \\fn build() u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0 };
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    return builder.store("a");
        \\}
    );
}

test "index-type-narrowing-wraparound: a receiver the caller never caps proves nothing" {
    try testing.expectFiresTyped(check, R,
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    fn store(self: *Builder, bytes: []const u8) u32 {
        \\        if (bytes.len > self.max_text_bytes) return 0;
        \\        const len: u32 = @intCast(bytes.len);
        \\        return len;
        \\    }
        \\};
        \\pub fn build(bytes: []const u8, ceiling: usize) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = ceiling };
        \\    return builder.store(bytes);
        \\}
    );
}

test "index-type-narrowing-wraparound: a ceiling only one of two callers writes does not reach the callee" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    fn store(self: *Builder, bytes: []const u8) u32 {
        \\        if (bytes.len > self.max_text_bytes) return 0;
        \\        const len: u32 = @intCast(bytes.len);
        \\        return len;
        \\    }
        \\};
        \\pub fn capped(bytes: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0 };
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    return builder.store(bytes);
        \\}
        \\pub fn uncapped(bytes: []const u8, ceiling: usize) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = ceiling };
        \\    return builder.store(bytes);
        \\}
    );
}

// The arena is a length COUNTER, and it really does grow: `self.len = end`
// moves a value the caller reads back.  The shape this replaces grew a slice
// into the bytes it already pointed at
// (`self.text = self.text[0 .. self.text.len + bytes.len]`), which is not a
// source that can run — the slice is exactly `len` long — so every fact about
// it described a program that traps on its first append.  A ceiling is a
// claim about a value the callee can actually write.
//
// The two guards are what make `grow` runnable: the first keeps a single
// append inside the ceiling, the second keeps the total inside it, and
// together they are why `self.len + bytes.len` cannot overflow at all.

test "index-type-narrowing-wraparound: a callee's own ceiling on the arena reaches the caller" {
    // The ceiling is written by the CALLER and read by the CALLEE, and what
    // comes back out is a bound on the length the callee left behind: the
    // arena starts inside the ceiling, and every path out of `grow` either
    // grew within it or declined and kept the length it was handed.  Both
    // calls are here because the contract is about what every call leaves,
    // not about the one that happened to prove something.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    len: usize,
        \\    fn grow(self: *Builder, bytes: []const u8) void {
        \\        if (bytes.len > self.max_text_bytes) return;
        \\        const end = self.len + bytes.len;
        \\        if (end > self.max_text_bytes) return;
        \\        self.len = end;
        \\    }
        \\};
        \\fn build(source: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    builder.len = 0;
        \\    builder.grow(source);
        \\    builder.grow("\n");
        \\    const total: u32 = @intCast(builder.len);
        \\    return total;
        \\}
    );
}

test "index-type-narrowing-wraparound: an arena a caller never bounds proves nothing" {
    // The ceiling is written, and it is the full range of the type: a guard
    // against it bounds the growth by nothing at all.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    len: usize,
        \\    fn grow(self: *Builder, bytes: []const u8) void {
        \\        if (bytes.len > self.max_text_bytes) return;
        \\        const end = self.len + bytes.len;
        \\        if (end > self.max_text_bytes) return;
        \\        self.len = end;
        \\    }
        \\};
        \\fn build(source: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    builder.max_text_bytes = std.math.maxInt(usize);
        \\    builder.len = 0;
        \\    builder.grow(source);
        \\    const total: u32 = @intCast(builder.len);
        \\    return total;
        \\}
    );
}

test "index-type-narrowing-wraparound: an arena a caller starts outside the ceiling is still outside it" {
    // The guards bound what the callee APPENDS.  The path where it declines
    // to append leaves the length it was handed exactly as it was, so a
    // caller that starts the arena past the ceiling has an arena past the
    // ceiling afterwards however many times it grows.  Installing the
    // ceiling outright would be the unsound reading here, not the strict one.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    len: usize,
        \\    fn grow(self: *Builder, bytes: []const u8) void {
        \\        if (bytes.len > self.max_text_bytes) return;
        \\        const end = self.len + bytes.len;
        \\        if (end > self.max_text_bytes) return;
        \\        self.len = end;
        \\    }
        \\};
        \\fn build(source: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    builder.len = source.len;
        \\    builder.grow(source);
        \\    const total: u32 = @intCast(builder.len);
        \\    return total;
        \\}
    );
}

test "index-type-narrowing-wraparound: a ceiling only one of two callers writes does not reach the caller either" {
    // The receiver contract is a claim about EVERY call of the function, so
    // the ceiling `capped` writes is not one `build` may read back: `grow` is
    // reached with the field as wide as the type says, and the consumer here
    // is left with an unbounded length it cannot cast.  One consumer, and it
    // is genuinely unsafe — the ceiling it was handed is the full range of
    // its type, which bounds the growth by nothing at all.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    len: usize,
        \\    fn grow(self: *Builder, bytes: []const u8) void {
        \\        if (bytes.len > self.max_text_bytes) return;
        \\        const end = self.len + bytes.len;
        \\        if (end > self.max_text_bytes) return;
        \\        self.len = end;
        \\    }
        \\};
        \\fn capped(source: []const u8) void {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    builder.len = 0;
        \\    builder.grow(source);
        \\}
        \\fn build(source: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    builder.max_text_bytes = std.math.maxInt(usize);
        \\    builder.len = 0;
        \\    builder.grow(source);
        \\    const total: u32 = @intCast(builder.len);
        \\    return total;
        \\}
    );
}

test "index-type-narrowing-wraparound: the arena's ceiling bounds the length, not a difference against a snapshot" {
    // What the contract exports is a bound on the value the callee left
    // behind.  A difference against a length the caller recorded before the
    // call is a different value, and this one is unbounded on its own: the
    // snapshot has no ceiling, so the difference can leave the destination
    // range even where the arena itself cannot.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: usize,
        \\    len: usize,
        \\    fn grow(self: *Builder, bytes: []const u8) void {
        \\        if (bytes.len > self.max_text_bytes) return;
        \\        const end = self.len + bytes.len;
        \\        if (end > self.max_text_bytes) return;
        \\        self.len = end;
        \\    }
        \\};
        \\fn build(source: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    const start = source.len;
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    builder.len = 0;
        \\    builder.grow(source);
        \\    const total: u32 = @intCast(builder.len - start);
        \\    return total;
        \\}
    );
}

test "index-type-narrowing-wraparound: a signed difference says nothing about the order of its operands" {
    // The ceiling is written down and it is still not a bound: `-|` saturates
    // at zero instead of going negative whenever the subtrahend is the larger
    // of the two, so nothing here orders the arena's length against the
    // ceiling and the callee cannot cap what it grows.  The guard's own
    // conversions are widenings rather than casts on purpose: a `usize`
    // length narrowed into a signed type is a separate conversion this rule
    // reports in its own right, and counting it here would make the fixture
    // assert a number about the guard instead of about the ceiling.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const max_u32 = std.math.maxInt(u32);
        \\const Builder = struct {
        \\    max_text_bytes: i128,
        \\    len: usize,
        \\    fn grow(self: *Builder, bytes: []const u8) void {
        \\        if (@as(i128, bytes.len) > self.max_text_bytes -| @as(i128, self.len)) return;
        \\        self.len = self.len + bytes.len;
        \\    }
        \\};
        \\fn build(source: []const u8) u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0, .len = 0 };
        \\    builder.max_text_bytes = @as(i128, max_u32);
        \\    builder.len = 0;
        \\    builder.grow(source);
        \\    const total: u32 = @intCast(builder.len);
        \\    return total;
        \\}
    );
}

// ── A value narrowed on its way into a subscript ──────────────────────────
//
// This is the length surface spelled as a use.  What settles it is the range
// the ORACLE proves AT THE CAST, and the collection's real capacity enters
// through the guard that already names it: `if (index >= array.len)` reads
// `array.len` at the type the collection actually has.  A `[128]u8` turns that
// guard into 127, which an `i8` names outright; a `[129]u8` turns it into 128,
// which it does not — a conversion that traps on an index the collection
// really admits, with nothing near the subscript saying so.
//
// The subscript itself is NOT the evidence, and the cases below are what keep
// that honest: a conversion that traps before the subscript ever runs is
// reported whatever the collection's size, and a capacity the guard never
// reaches is not a bound on anything.

test "index-type-narrowing-wraparound: a narrowing into a subscript is answered by the capacity it indexes" {
    // The two bodies differ in one digit: 128 lets the guard through with 127,
    // which an `i8` names; 129 lets it through with 128, which it does not.
    try testing.expectNoFireTyped(check,
        \\fn fits_capacity(array: *const [128]u8, index: u16) ?u8 {
        \\    if (index >= array.len) return null;
        \\    const narrow: i8 = @intCast(index);
        \\    return array[@intCast(narrow)];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn overflows_capacity(array: *const [129]u8, index: u16) ?u8 {
        \\    if (index >= array.len) return null;
        \\    const narrow: i8 = @intCast(index);
        \\    return array[@intCast(narrow)];
        \\}
    );
}

test "index-type-narrowing-wraparound: a capacity the guard never reaches bounds nothing" {
    // The same 129 elements as the body above, and silent here because the
    // GUARD stops at 99 — not because the collection is small.  Reading the
    // subscript as the bound reports this on every call; reading the capacity
    // as the bound reports it too, for the same index either way.  Only the
    // range the oracle proved is an answer.
    try testing.expectNoFireTyped(check,
        \\fn guard_says_ninety_nine(array: *const [129]u8, index: u16) u8 {
        \\    if (index >= 100) return 0;
        \\    const narrow: i8 = @intCast(index);
        \\    return array[@intCast(narrow)];
        \\}
    );
}

test "index-type-narrowing-wraparound: a value too large for the destination traps before the subscript does" {
    // `raw` runs to 65535 and the table holds three elements, so the SUBSCRIPT
    // would reject most of it anyway.  But `raw = 256` is rejected by the
    // CONVERSION, a line earlier and for its own reason, and a rule that
    // takes the collection's capacity as a ceiling is calling that conversion
    // safe on the strength of a subscript that never runs.
    try testing.expectFiresTyped(check, R,
        \\const table = [_]u8{ 10, 20, 30 };
        \\fn truncating(raw: u16) u8 {
        \\    const index: u8 = @intCast(raw);
        \\    return table[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: a negative index traps before the subscript does" {
    // The same shape from the other side: `-1` is not a subscript a
    // three-element array admits either, and `@intCast` refuses to make one
    // out of it before the array is ever asked.
    try testing.expectFiresTyped(check, R,
        \\fn signed_index(array: *const [3]u8, index: i8) u8 {
        \\    const at: usize = @intCast(index);
        \\    return array[at];
        \\}
    );
}

test "index-type-narrowing-wraparound: a small table read through a signed sentinel is not automatically a defect" {
    // The narrowing is guarded by the value it guards: nothing above 127
    // reaches the conversion, so `i8` names every value that does.  The table
    // being three elements long makes `table[3..127]` an out-of-range
    // subscript — a fact about the ACCESS, and another rule's to report, not
    // a wraparound in the conversion.
    try testing.expectNoFireTyped(check,
        \\const table = [_]u8{ 10, 20, 30 };
        \\fn classify(raw: u8) u8 {
        \\    if (raw > 127) return 0;
        \\    const index: i8 = @intCast(raw);
        \\    return table[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: the narrowed value reaches the subscript through a local alias" {
    try testing.expectFiresTyped(check, R,
        \\fn through_alias(array: *const [129]u8, index: u16) u8 {
        \\    const narrow: i8 = @intCast(index);
        \\    const at = narrow;
        \\    return array[at];
        \\}
    );
}

test "index-type-narrowing-wraparound: a conditional rewrite does not hide the conversion the other path still uses" {
    // On the path where the rewrite does not happen the subscript reads
    // exactly what the cast wrote, and `@intCast` traps there for any index
    // from 128 up.  Whether a local is written later — on one path or on all
    // of them — is a fact about the CONSUMER, and a consumer never makes the
    // conversion in front of it sound.
    try testing.expectFiresTyped(check, R,
        \\fn rewritten(array: *const [129]u8, index: u16) u8 {
        \\    var narrow: i8 = @intCast(index);
        \\    if (narrow == 0) narrow = 1;
        \\    return array[narrow];
        \\}
    );
}

test "index-type-narrowing-wraparound: a write after the subscript does not retroactively remove the conversion" {
    // The subscript reads the cast's value before the rewrite is reached.  An
    // account of "is this local written" that has no order in it drops the
    // link here just the same, which is the whole reason the account is gone.
    try testing.expectFiresTyped(check, R,
        \\fn written_after(array: *const [129]u8, index: u16) u8 {
        \\    var narrow: i8 = @intCast(index);
        \\    const value = array[@intCast(narrow)];
        \\    narrow = 0;
        \\    return value;
        \\}
    );
}

test "index-type-narrowing-wraparound: an alias taken before a rewrite still carries the conversion" {
    // `saved` captured what the cast wrote before `narrow` was overwritten,
    // and `saved` is the name the subscript reads.  The hop from `saved` back
    // to `narrow` has to survive the write for this to be reported at all.
    try testing.expectFiresTyped(check, R,
        \\fn alias_taken_first(array: *const [129]u8, index: u16) u8 {
        \\    var narrow: i8 = @intCast(index);
        \\    const saved = narrow;
        \\    narrow = 0;
        \\    return array[@intCast(saved)];
        \\}
    );
}

test "index-type-narrowing-wraparound: a shadowing local is a different value from the one the cast produced" {
    // The cast's `narrow` is scoped to the block above; the one the subscript
    // names is the declaration below it, written from a literal.  Following
    // the SPELLING would connect the cast to a subscript it does not feed.
    try testing.expectNoFireTyped(check,
        \\fn shadowed(array: *const [129]u8, index: u16) u8 {
        \\    {
        \\        const narrow: i8 = @intCast(index);
        \\        _ = narrow;
        \\    }
        \\    const narrow: i8 = 0;
        \\    return array[narrow];
        \\}
    );
}

test "index-type-narrowing-wraparound: an index into a runtime-sized collection is a finding, not a proof" {
    // A slice admits no capacity this rule can read, so the oracle's facts
    // are all there is — and `u16` reaching an `i8` is not one of them.
    try testing.expectFiresTyped(check, R,
        \\fn unbounded(array: []const u8, index: u16) u8 {
        \\    const narrow: i8 = @intCast(index);
        \\    return array[narrow];
        \\}
    );
}

test "index-type-narrowing-wraparound: a numeric conversion that never reaches a subscript is not this rule's business" {
    // Both casts narrow past their destination.  Neither result subscripts
    // anything, so there is no collection to measure either against, and a
    // rule answering from the source's width alone would report them.
    try testing.expectNoFireTyped(check,
        \\fn halve(value: u16) u8 {
        \\    const narrowed: u8 = @intCast(value / 2);
        \\    return narrowed;
        \\}
        \\fn total(counts: []const u8) u32 {
        \\    var sum: u32 = 0;
        \\    for (counts) |count| sum += @intCast(count);
        \\    return sum;
        \\}
    );
}

test "index-type-narrowing-wraparound: a length cast keeps its own proof beside an indexed one" {
    // The two surfaces are asked separately and each answers for itself: a
    // `[200]u8` is 200 elements long, which an `u8` names outright, and every
    // one of those elements is a subscript an `i8` does not.
    try testing.expectNoFireTyped(check,
        \\fn measured(array: *const [100]u8, index: u16) u8 {
        \\    const width: u8 = @intCast(array.len);
        \\    if (index >= array.len) return width;
        \\    const narrow: i8 = @intCast(index);
        \\    return array[@intCast(narrow)] + width;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn measured(array: *const [200]u8, index: u16) u8 {
        \\    const width: u8 = @intCast(array.len);
        \\    if (index >= array.len) return width;
        \\    const narrow: i8 = @intCast(index);
        \\    return array[@intCast(narrow)] + width;
        \\}
    );
}

test "index-type-narrowing-wraparound: a by-value slice header survives calls and aliased element writes" {
    try testing.expectNoFireTyped(check,
        \\const Holder = struct { bytes: [32]u8 };
        \\fn inspect(bytes: []const u8) void { _ = bytes; }
        \\fn copy(holder: *Holder, bytes: []const u8) u8 {
        \\    if (bytes.len > 32) return 0;
        \\    inspect(bytes);
        \\    holder.bytes[0] = 1;
        \\    @memcpy(holder.bytes[0..bytes.len], bytes);
        \\    return @intCast(bytes.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn resize(bytes: *[]const u8, replacement: []const u8) void {
        \\    bytes.* = replacement;
        \\}
        \\fn copy(bytes: *[]const u8, replacement: []const u8) u8 {
        \\    if (bytes.len > 32) return 0;
        \\    resize(bytes, replacement);
        \\    return @intCast(bytes.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: exhaustive enum tags bound an index conversion" {
    try testing.expectNoFireTyped(check,
        \\const Tag = enum(i32) { first = 0, last = 7 };
        \\fn read(bytes: []const u8, tag: Tag) u8 {
        \\    const index: u8 = @intCast(@intFromEnum(tag));
        \\    return bytes[index];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Tag = enum(i32) { first = -1, last = 7 };
        \\fn read(bytes: []const u8, tag: Tag) u8 {
        \\    const index: u8 = @intCast(@intFromEnum(tag));
        \\    return bytes[index];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Tag = enum(u32) { first = 0, last = 7, _ };
        \\fn read(bytes: []const u8, tag: Tag) u8 {
        \\    const index: u8 = @intCast(@intFromEnum(tag));
        \\    return bytes[index];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Tag = enum(u32) { first = 0, last = 256 };
        \\fn read(bytes: []const u8, tag: Tag) u8 {
        \\    const index: u8 = @intCast(@intFromEnum(tag));
        \\    return bytes[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: only returning selector arms bound a conversion" {
    try testing.expectNoFireTyped(check,
        \\const Kind = enum { buffer, sampler, absent };
        \\fn descriptor(kind: Kind, dynamic: bool) i32 {
        \\    return switch (kind) {
        \\        .buffer => if (dynamic) 8 else 6,
        \\        .sampler => 0,
        \\        .absent => unreachable,
        \\    };
        \\}
        \\pub fn read(bytes: []const u8, kind: Kind, dynamic: bool) u8 {
        \\    const index: usize = @intCast(descriptor(kind, dynamic));
        \\    return bytes[index];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Kind = enum { buffer, sampler, absent };
        \\fn descriptor(kind: Kind, dynamic: bool) i32 {
        \\    return switch (kind) {
        \\        .buffer => if (dynamic) 8 else -1,
        \\        .sampler => 0,
        \\        .absent => unreachable,
        \\    };
        \\}
        \\pub fn read(bytes: []const u8, kind: Kind, dynamic: bool) u8 {
        \\    const index: usize = @intCast(descriptor(kind, dynamic));
        \\    return bytes[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: selector return summaries retain wide and open arms" {
    try testing.expectFiresTyped(check, R,
        \\const Kind = enum { small, large, absent };
        \\fn descriptor(kind: Kind) u16 {
        \\    return switch (kind) {
        \\        .small => 7,
        \\        .large => 256,
        \\        .absent => unreachable,
        \\    };
        \\}
        \\pub fn read(bytes: []const u8, kind: Kind) u8 {
        \\    const index: u8 = @intCast(descriptor(kind));
        \\    return bytes[index];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Kind = enum { small, open, absent };
        \\fn descriptor(kind: Kind, raw: i32) i32 {
        \\    return switch (kind) {
        \\        .small => 7,
        \\        .open => raw,
        \\        .absent => unreachable,
        \\    };
        \\}
        \\pub fn read(bytes: []const u8, kind: Kind, raw: i32) u8 {
        \\    const index: usize = @intCast(descriptor(kind, raw));
        \\    return bytes[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: selector effects cannot reuse pre-return facts" {
    try testing.expectFiresTyped(check, R,
        \\fn rewrite(value: *i32) bool {
        \\    value.* = -1;
        \\    return true;
        \\}
        \\fn descriptor() i32 {
        \\    var value: i32 = 0;
        \\    return if (rewrite(&value)) value else unreachable;
        \\}
        \\pub fn read(bytes: []const u8) u8 {
        \\    const index: usize = @intCast(descriptor());
        \\    return bytes[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: selector captures retain their signed domain" {
    try testing.expectFiresTyped(check, R,
        \\fn descriptor(candidate: ?i32) i32 {
        \\    return if (candidate) |value| value else 0;
        \\}
        \\pub fn read(bytes: []const u8, candidate: ?i32) u8 {
        \\    const index: usize = @intCast(descriptor(candidate));
        \\    return bytes[index];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Kind = union(enum) { candidate: i32, absent };
        \\fn descriptor(kind: Kind) i32 {
        \\    return switch (kind) {
        \\        .candidate => |value| value,
        \\        .absent => 0,
        \\    };
        \\}
        \\pub fn read(bytes: []const u8, kind: Kind) u8 {
        \\    const index: usize = @intCast(descriptor(kind));
        \\    return bytes[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: unknown selector calls keep the declared range" {
    try testing.expectFiresTyped(check, R,
        \\extern fn unknown() i32;
        \\const Kind = enum { known, unknown, absent };
        \\fn descriptor(kind: Kind) i32 {
        \\    return switch (kind) {
        \\        .known => 0,
        \\        .unknown => unknown(),
        \\        .absent => unreachable,
        \\    };
        \\}
        \\pub fn read(bytes: []const u8, kind: Kind) u8 {
        \\    const index: usize = @intCast(descriptor(kind));
        \\    return bytes[index];
        \\}
    );
}

test "index-type-narrowing-wraparound: explicit as supplies only its own cast destination" {
    try testing.expectNoFireTyped(check,
        \\fn size(bytes: []const u8) u64 {
        \\    return @as(u64, @intCast(bytes.len));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn size(bytes: []const u8) u64 {
        \\    return @as(u64, @as(u8, @intCast(bytes.len)));
        \\}
    );
}

test "index-type-narrowing-wraparound: compound assignments supply integer destinations" {
    try testing.expectNoFireTyped(check,
        \\const Counts = struct { bytes: u64 = 0 };
        \\fn size(bytes: []const u8) u64 {
        \\    var counts: Counts = .{};
        \\    counts.bytes += @intCast(bytes.len);
        \\    counts.bytes ^= @intCast(bytes.len);
        \\    return counts.bytes;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn size(bytes: []const u8) u8 {
        \\    var count: u8 = 0;
        \\    count += @intCast(bytes.len);
        \\    return count;
        \\}
    );
}

test "index-type-narrowing-wraparound: aggregate call fields retain their integer domains" {
    try testing.expectNoFireTyped(check,
        \\const Charge = struct { nodes: u64 };
        \\fn charge(_: Charge) void {}
        \\fn size(bytes: []const u8) void {
        \\    charge(.{ .nodes = @intCast(bytes.len) });
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Op = union(enum) { push: u16 };
        \\fn emit(_: Op) void {}
        \\fn size(bytes: []const u8) void {
        \\    if (bytes.len > 65535) return;
        \\    emit(.{ .push = @intCast(bytes.len) });
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Op = union(enum) { push: u16 };
        \\fn emit(_: Op) void {}
        \\fn size(bytes: []const u8) void {
        \\    emit(.{ .push = @intCast(bytes.len) });
        \\}
    );
}

test "index-type-narrowing-wraparound: asserted returned aggregate fields retain bounds" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Result = struct { count: u32 };
        \\fn size(bytes: []const u8) Result {
        \\    std.debug.assert(bytes.len <= std.math.maxInt(u32));
        \\    return .{ .count = @intCast(bytes.len) };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Result = struct { count: u32 };
        \\fn size(bytes: []const u8) Result {
        \\    return .{ .count = @intCast(bytes.len) };
        \\}
    );
}

test "index-type-narrowing-wraparound: nested length candidates do not make widening unsafe" {
    try testing.expectNoFireTyped(check,
        \\fn select(indexes: []const u32, index: usize) usize {
        \\    return @as(usize, @intCast(indexes[@min(index, indexes.len - 1)]));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn select(indexes: []const u32, index: usize) u8 {
        \\    return @as(u8, @intCast(indexes[@min(index, indexes.len - 1)]));
        \\}
    );
}

test "index-type-narrowing-wraparound: logarithm length results widen without a length bound" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn size(bytes: []const u8) u64 {
        \\    return @as(u64, @intCast(std.math.log2_int_ceil(usize, bytes.len)));
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn size(bytes: []const u8) u7 {
        \\    return @as(u7, @intCast(std.math.log2_int_ceil(usize, bytes.len)));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn size(bytes: []const u8) u1 {
        \\    return @as(u1, @intCast(std.math.log2_int_ceil(usize, bytes.len)));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Math = struct {
        \\    fn log2_int_ceil(comptime T: type, value: T) T { return value; }
        \\};
        \\fn size(bytes: []const u8) u7 {
        \\    return @as(u7, @intCast(Math.log2_int_ceil(usize, bytes.len)));
        \\}
    );
}

test "index-type-narrowing-wraparound: closed fixture callers preserve literal slice extents" {
    try testing.expectNoFireTyped(check,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\test "literal callers" {
        \\    _ = fixture(&.{ 1, 2, 3 });
        \\    _ = fixture("hello\n");
        \\    const fixed = [_]u8{ 1, 2, 3, 4 };
        \\    _ = fixture(&fixed);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\fn forward(values: []const u8) u8 {
        \\    return fixture(values);
        \\}
        \\test "closed forwarding caller" {
        \\    _ = forward(@as([]const u8, &.{ 1, 2, 3 }));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\test "one oversized caller" {
        \\    _ = fixture("small");
        \\    _ = fixture(&([_]u8{0} ** 256));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\pub fn open(values: []const u8) u8 {
        \\    _ = fixture("small");
        \\    return fixture(values);
        \\}
    );
}

test "index-type-narrowing-wraparound: caller extents use the current slice header" {
    try testing.expectFiresTyped(check, R,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\pub fn caller(input: []const u8) u8 {
        \\    var values: []const u8 = "small";
        \\    values = input;
        \\    return fixture(values);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn fixture(values: []const u8, _: void) u8 {
        \\    return @intCast(values.len);
        \\}
        \\fn replace(values: *[]const u8, input: []const u8) void {
        \\    values.* = input;
        \\}
        \\pub fn caller(input: []const u8) u8 {
        \\    var values: []const u8 = "small";
        \\    return fixture(values, replace(&values, input));
        \\}
    );
}

test "index-type-narrowing-wraparound: unrelated std allocation keeps a copied scalar length guard" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Process = struct { exported: std.ArrayList(u8) = .empty };
        \\const State = struct { map: std.StringHashMapUnmanaged(u8) = .empty };
        \\pub fn exported(process: *Process, alloc: std.mem.Allocator) !void {
        \\    const length = process.exported.items.len;
        \\    if (length > 1024) return error.Unsupported;
        \\    const state = try alloc.create(State);
        \\    defer alloc.destroy(state);
        \\    state.* = .{};
        \\    try state.map.ensureUnusedCapacity(alloc, @intCast(length));
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Holder = struct { items: []const u8 = &.{} };
        \\pub fn count(holder: *Holder, alloc: std.mem.Allocator) !u8 {
        \\    const length = holder.items.len;
        \\    if (length > 255) return error.Unsupported;
        \\    const other = try alloc.create(Holder);
        \\    const alias = other;
        \\    alias.* = .{};
        \\    alias.items = &.{};
        \\    return @intCast(length);
        \\}
    );
}

test "index-type-narrowing-wraparound: custom and unknown factories cannot certify unrelated storage" {
    try testing.expectFiresTyped(check, R,
        \\const Holder = struct { items: []const u8 = &.{} };
        \\const Factory = struct {
        \\    target: *Holder,
        \\    fn create(self: Factory, comptime T: type) !*T { return self.target; }
        \\};
        \\pub fn count(holder: *Holder, replacement: []const u8) !u8 {
        \\    if (holder.items.len > 255) return error.Unsupported;
        \\    const factory = Factory{ .target = holder };
        \\    const other = try factory.create(Holder);
        \\    other.* = .{ .items = replacement };
        \\    return @intCast(holder.items.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Holder = struct { items: []const u8 = &.{} };
        \\extern fn factory() *Holder;
        \\pub fn count(holder: *Holder, replacement: []const u8) u8 {
        \\    if (holder.items.len > 255) return 0;
        \\    const other = factory();
        \\    other.* = .{ .items = replacement };
        \\    return @intCast(holder.items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: successful scalar helper bounds checked argument lengths" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(args: []const u8) !u32 {
        \\    const nargs = std.math.add(usize, args.len, 1) catch return error.Overflow;
        \\    try checkCount(nargs);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(args: []const u8) !u8 {
        \\    const nargs = try std.math.add(usize, args.len, 1);
        \\    try checkCount(nargs);
        \\    return @intCast(args.len + 1);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn allocBlock(alloc: std.mem.Allocator, count: usize) ![]u8 {
        \\    if (count == 0 or count > 255) return error.InvalidCount;
        \\    return try alloc.alloc(u8, count);
        \\}
        \\pub fn count(args: []const u8, alloc: std.mem.Allocator) !u8 {
        \\    const nargs = std.math.add(usize, args.len, 1) catch return error.Overflow;
        \\    const block = try allocBlock(alloc, nargs);
        \\    defer alloc.free(block);
        \\    return @intCast(args.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: failed or unknown scalar helpers do not bound arguments" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(args: []const u8) !u32 {
        \\    const nargs = std.math.add(usize, args.len, 1) catch return error.Overflow;
        \\    checkCount(nargs) catch {};
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\extern fn checkCount(count: usize) anyerror!void;
        \\pub fn count(args: []const u8) !u32 {
        \\    const nargs = std.math.add(usize, args.len, 1) catch return error.Overflow;
        \\    try checkCount(nargs);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(args: []const u8) !u32 {
        \\    const nargs = std.math.add(usize, args.len, 1) catch 0;
        \\    try checkCount(nargs);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\fn relay(count: usize) !void {
        \\    try checkCount(count);
        \\}
        \\pub fn count(args: []const u8) u32 {
        \\    const result = relay(args.len);
        \\    result catch {};
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn checkCount(count: usize, skip: bool) !void {
        \\    if (skip) return;
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(args: []const u8, skip: bool) !u32 {
        \\    try checkCount(args.len, skip);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn checkCount(input: usize) !void {
        \\    const count = @min(input, 255);
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(args: []const u8) !u32 {
        \\    try checkCount(args.len);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(input: []const u8, replacement: []const u8) !u32 {
        \\    var args = input;
        \\    const nargs = try std.math.add(usize, args.len, 1);
        \\    args = replacement;
        \\    try checkCount(nargs);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checkCount(count: usize) !void {
        \\    if (count > 255) return error.TooMany;
        \\}
        \\pub fn count(input: []const u8, replacement: []const u8) !u32 {
        \\    var args = input;
        \\    const alias = &args;
        \\    const nargs = try std.math.add(usize, args.len, 1);
        \\    alias.* = replacement;
        \\    try checkCount(nargs);
        \\    return @intCast(args.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn checkCount(count: usize, args: *[]const u8, replacement: []const u8) !void {
        \\    if (count > 255) return error.TooMany;
        \\    args.* = replacement;
        \\}
        \\pub fn count(input: []const u8, replacement: []const u8) !u32 {
        \\    var args = input;
        \\    try checkCount(args.len, &args, replacement);
        \\    return @intCast(args.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: successful aggregate returns bound their slice fields" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Event = struct { raw: []const u8 };
        \\const Word = packed struct { kind: u8, payload: u24, offset: u32 };
        \\fn emit(input: []const u8) !Event {
        \\    if (input.len > std.math.maxInt(u24)) return error.TapeTooLarge;
        \\    return .{ .raw = input };
        \\}
        \\pub fn word(input: []const u8) !Word {
        \\    const value = try emit(input);
        \\    return .{ .kind = 0, .payload = @intCast(value.raw.len), .offset = 0 };
        \\}
        \\pub fn length(input: []const u8, out: *u32) !void {
        \\    const value = try emit(input);
        \\    out.* = @intCast(value.raw.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Event = struct { raw: []const u8 };
        \\fn emit(input: []const u8, offset: usize, length: usize, empty: bool) !Event {
        \\    if (length > 16777215) return error.TapeTooLarge;
        \\    if (empty) return .{ .raw = input[0..0] };
        \\    return .{ .raw = input[offset..offset + length] };
        \\}
        \\pub fn length(input: []const u8, offset: usize, count: usize, empty: bool) !u24 {
        \\    const value = try emit(input, offset, count, empty);
        \\    return @intCast(value.raw.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: opaque replaced and alternate returned slice fields remain unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 };
        \\extern fn emit(input: []const u8) anyerror!Event;
        \\pub fn length(input: []const u8) !u24 {
        \\    const value = try emit(input);
        \\    return @intCast(value.raw.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 };
        \\fn emit(input: []const u8, other: []const u8, alternate: bool) !Event {
        \\    if (input.len > 16777215) return error.TapeTooLarge;
        \\    if (alternate) return .{ .raw = other };
        \\    return .{ .raw = input };
        \\}
        \\pub fn length(input: []const u8, other: []const u8, alternate: bool) !u24 {
        \\    const value = try emit(input, other, alternate);
        \\    return @intCast(value.raw.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 };
        \\fn emit(input: []const u8) !Event {
        \\    if (input.len > 16777215) return error.TapeTooLarge;
        \\    return .{ .raw = input };
        \\}
        \\pub fn length(input: []const u8, other: []const u8) !u24 {
        \\    var value = try emit(input);
        \\    value.raw = other;
        \\    return @intCast(value.raw.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 };
        \\fn emit(input: []const u8) !Event {
        \\    if (input.len > 16777215) return error.TapeTooLarge;
        \\    return .{ .raw = input };
        \\}
        \\pub fn length(input: []const u8, other: []const u8) u24 {
        \\    const value = emit(input) catch Event{ .raw = other };
        \\    return @intCast(value.raw.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: fixed shape helper callers preserve container extents" {
    try testing.expectNoFireTyped(check,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\fn shape() [4]u8 {
        \\    return .{ 1, 2, 3, 4 };
        \\}
        \\test "fixed array result" {
        \\    _ = fixture(&shape());
        \\    const values: []const u8 = @as([]const u8, "small");
        \\    _ = fixture(values);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\extern fn shape() [256]u8;
        \\test "oversized array result" {
        \\    _ = fixture(&shape());
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn fixture(values: []const u8) u8 {
        \\    return @intCast(values.len);
        \\}
        \\extern fn shape() []const u8;
        \\test "dynamic result" {
        \\    _ = fixture(shape());
        \\}
    );
}

test "index-type-narrowing-wraparound: relative embedded byte counts prove only fitting lengths" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "small.bin", .data = "hello" });
    try tmp.dir.writeFile(io, .{ .sub_path = "large.bin", .data = &([_]u8{0} ** 256) });
    try tmp.dir.createDir(io, "directory", .default_dir);
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const source_path = try std.fs.path.join(gpa, &.{ root, "main.zig" });
    defer gpa.free(source_path);
    const cases = [_]struct {
        source: [:0]const u8,
        count: usize,
        excluded: bool = false,
        source_error: ?file_cache_mod.SummaryError = null,
    }{
        .{ .source =
        \\const bytes = @embedFile("./small\x2ebin");
        \\pub fn rootLength() u8 { return @intCast(bytes.len); }
        \\pub fn localLength() u8 {
        \\    const original = @embedFile("small.bin");
        \\    const alias = original;
        \\    return @intCast(alias.len);
        \\}
        \\pub fn directLength() u8 { return @intCast(@embedFile("small.bin").len); }
        , .count = 0 },
        .{ .source =
        \\const bytes = @embedFile("large.bin");
        \\pub fn length() u8 { return @intCast(bytes.len); }
        , .count = 1 },
        .{ .source =
        \\const bytes = @embedFile("missing.bin");
        \\pub fn length() u8 { return @intCast(bytes.len); }
        , .count = 0, .source_error = error.FileNotFound },
        .{ .source =
        \\const filename = "small.bin";
        \\const bytes = @embedFile(filename);
        \\pub fn length() u8 { return @intCast(bytes.len); }
        , .count = 1 },
        .{ .source =
        \\const bytes = @embedFile("directory");
        \\pub fn length() u8 { return @intCast(bytes.len); }
        , .count = 1 },
        .{ .source =
        \\const bytes = @embedFile("small.bin");
        \\pub fn length() u8 { return @intCast(bytes.len); }
        , .count = 1, .excluded = true },
    };
    for (cases) |case| {
        try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = case.source });
        var context: type_resolver_mod.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{
            .roots = &.{root},
            .excludes = if (case.excluded) &.{"small.bin"} else &.{},
        };
        var resolver: type_resolver_mod.TypeResolver = undefined;
        try resolver.init(&context, gpa, source_path, case.source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
        var cache = file_cache_mod.FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        cache.file_path = source_path;
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer testing.freeProblems(gpa, &problems);
        if (case.source_error) |err| {
            try std.testing.expectError(err, check(gpa, tree, &cache, &config_mod.Default, &problems));
            try std.testing.expectEqual(@as(usize, 0), cache.embedded_file_lengths.count());
        } else {
            try check(gpa, tree, &cache, &config_mod.Default, &problems);
        }
        try std.testing.expectEqual(case.count, problems.items.len);
        for (problems.items) |finding| try std.testing.expectEqualStrings(R, finding.rule_id);
    }
}

test "index-type-narrowing-wraparound: unproved embedded extents remain conservative" {
    try testing.expectFiresTyped(check, R,
        \\const bytes = @embedFile("unresolved_named_data");
        \\pub fn length() u8 {
        \\    return @intCast(bytes.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: writes to fresh allocation aliases still retire their guards" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Holder = struct { items: []const u8 = &.{} };
        \\pub fn count(alloc: std.mem.Allocator, input: []const u8, replacement: []const u8) !u8 {
        \\    const other = try alloc.create(Holder);
        \\    other.* = .{ .items = input };
        \\    const alias = other;
        \\    if (alias.items.len > 255) return error.Unsupported;
        \\    other.* = .{ .items = replacement };
        \\    return @intCast(alias.items.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Holder = struct { items: []const u8 = &.{} };
        \\pub fn count(alloc: std.mem.Allocator, input: []const u8, replacement: []const u8) !u8 {
        \\    const other = try alloc.create(Holder);
        \\    other.* = .{ .items = input };
        \\    const alias = other;
        \\    if (alias.items.len > 255) return error.Unsupported;
        \\    other.items = replacement;
        \\    return @intCast(alias.items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: opaque length fields do not imply usize" {
    try testing.expectNoFireTyped(check,
        \\fn size(bytes: []const u8) u64 {
        \\    return @intCast(bytes.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn size(source: anytype) u64 {
        \\    return @intCast(source.items.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Source = struct { items: struct { len: u128 } };
        \\pub fn size(source: Source) u64 {
        \\    return @intCast(source.items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: returned nested header copies keep their field extents" {
    try testing.expectNoFireTyped(check,
        \\const Event = struct { span: struct { slice: []const u8 }, tag: u8 };
        \\fn emit(input: []const u8) !Event {
        \\    if (input.len > 16777215) return error.TooLarge;
        \\    const event = Event{ .span = .{ .slice = input }, .tag = 0 };
        \\    const copy = event;
        \\    return copy;
        \\}
        \\pub fn length(input: []const u8) !u24 {
        \\    const event = try emit(input);
        \\    const copy = event;
        \\    return @intCast(copy.span.slice.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: returned headers reject stale missing or effectful extents" {
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 };
        \\fn emit(input: []const u8, other: []const u8) !Event {
        \\    if (input.len > 16777215) return error.TooLarge;
        \\    var event = Event{ .raw = input };
        \\    event.raw = other;
        \\    return event;
        \\}
        \\pub fn length(input: []const u8, other: []const u8) !u24 {
        \\    const event = try emit(input, other);
        \\    return @intCast(event.raw.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 = undefined };
        \\fn emit(input: []const u8, omitted: bool) !Event {
        \\    if (input.len > 16777215) return error.TooLarge;
        \\    if (omitted) return .{};
        \\    return .{ .raw = input };
        \\}
        \\pub fn length(input: []const u8, omitted: bool) !u24 {
        \\    const event = try emit(input, omitted);
        \\    return @intCast(event.raw.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8, tag: u8 };
        \\fn replace(input: *[]const u8, other: []const u8) u8 {
        \\    input.* = other;
        \\    return 0;
        \\}
        \\fn emit(input: []const u8, other: []const u8) !Event {
        \\    if (input.len > 16777215) return error.TooLarge;
        \\    var raw = input;
        \\    return .{ .tag = replace(&raw, other), .raw = raw };
        \\}
        \\pub fn length(input: []const u8, other: []const u8) !u24 {
        \\    const event = try emit(input, other);
        \\    return @intCast(event.raw.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Event = struct { raw: []const u8 };
        \\fn emit(input: []const u8) !Event {
        \\    if (input.len > 16777215) return error.TooLarge;
        \\    defer opaqueValue();
        \\    return .{ .raw = input };
        \\}
        \\extern fn opaqueValue() void;
        \\pub fn length(input: []const u8) !u24 {
        \\    const event = try emit(input);
        \\    return @intCast(event.raw.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean indexed headers and nested metrics use field destinations" {
    try testing.expectNoFireTyped(check,
        \\const Header = struct { size: u64 };
        \\const Builder = struct { metrics: struct { bytes: u64 } };
        \\pub fn write(headers: []Header, index: usize, bytes: []const u8) void {
        \\    headers[index] = .{ .size = @intCast(bytes.len) };
        \\}
        \\pub fn init(bytes: []const u8) Builder {
        \\    return .{ .metrics = .{ .bytes = @intCast(bytes.len) } };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Header = struct { size: u32 };
        \\pub fn write(headers: []Header, index: usize, bytes: []const u8) void {
        \\    headers[index] = .{ .size = @intCast(bytes.len) };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Builder = struct { metrics: struct { bytes: u32 } };
        \\pub fn init(bytes: []const u8) Builder {
        \\    return .{ .metrics = .{ .bytes = @intCast(bytes.len) } };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn init(bytes: []const u8) MissingBuilder {
        \\    return .{ .metrics = .{ .bytes = @intCast(bytes.len) } };
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean nested assignment keeps fixed input count bounds" {
    try testing.expectNoFireTyped(check,
        \\const Input = struct { id: u32 };
        \\const SourceIdentity = struct { function_count: u32 };
        \\const ModuleInput = struct { source_identity: SourceIdentity };
        \\const Fixture = struct {
        \\    inputs: [3]Input,
        \\    module_input: ModuleInput,
        \\    pub fn init(self: *Fixture) void {
        \\        self.module_input = .{
        \\            .source_identity = .{ .function_count = @intCast(self.inputs.len) },
        \\        };
        \\    }
        \\};
        \\pub fn fixtureCount(fixture: *Fixture) u32 {
        \\    fixture.init();
        \\    return fixture.module_input.source_identity.function_count;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Input = struct { id: u32 };
        \\const SourceIdentity = struct { function_count: u32 };
        \\const ModuleInput = struct { source_identity: SourceIdentity };
        \\const Fixture = struct {
        \\    inputs: []const Input,
        \\    module_input: ModuleInput,
        \\    pub fn init(self: *Fixture) void {
        \\        self.module_input = .{
        \\            .source_identity = .{ .function_count = @intCast(self.inputs.len) },
        \\        };
        \\    }
        \\};
        \\pub fn fixtureCount(fixture: *Fixture) u32 {
        \\    fixture.init();
        \\    return fixture.module_input.source_identity.function_count;
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean named error unions retain bounded and widening destinations" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Function = @This();
        \\pub const CreateError = std.mem.Allocator.Error || error{ Full, Invalid };
        \\const State = struct {
        \\    pub fn count(ids: []const u32) Function.CreateError!u32 {
        \\        if (ids.len > std.math.maxInt(u32)) return error.Full;
        \\        return @intCast(ids.len);
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Function = @This();
        \\pub const CreateError = std.mem.Allocator.Error || error{ Full, Invalid };
        \\const State = struct {
        \\    pub fn count(ids: []const u32) Function.CreateError!u32 {
        \\        return @intCast(ids.len);
        \\    }
        \\};
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const EmitError = std.mem.Allocator.Error || error{InvalidInput};
        \\pub fn preambleLength(allocator: std.mem.Allocator, source: []const u8) EmitError!u64 {
        \\    var buf: std.ArrayList(u8) = .empty;
        \\    defer buf.deinit(allocator);
        \\    try buf.appendSlice(allocator, source);
        \\    return @intCast(buf.items.len);
        \\}
        \\pub fn plainLength(bytes: []const u8) !u64 {
        \\    return @intCast(bytes.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const EmitError = std.mem.Allocator.Error || error{InvalidInput};
        \\pub fn preambleLength(allocator: std.mem.Allocator, source: []const u8) EmitError!u32 {
        \\    var buf: std.ArrayList(u8) = .empty;
        \\    defer buf.deinit(allocator);
        \\    try buf.appendSlice(allocator, source);
        \\    return @intCast(buf.items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean Token length field uses its declared integer width" {
    try testing.expectNoFireTyped(check,
        \\pub const Token = struct {
        \\    start: u32,
        \\    len: u16,
        \\    pub fn span(self: Token, source: []const u8) []const u8 {
        \\        return source[@intCast(self.start) .. @as(usize, @intCast(self.start)) + @as(usize, @intCast(self.len))];
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\pub const Token = struct {
        \\    start: u32,
        \\    len: u128,
        \\    pub fn span(self: Token, source: []const u8) []const u8 {
        \\        return source[@intCast(self.start) .. @as(usize, @intCast(self.start)) + @as(usize, @intCast(self.len))];
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn span(token: anytype, source: []const u8) []const u8 {
        \\    return source[0 .. @as(usize, @intCast(token.len))];
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean unchecked SourceId file counts remain unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const SourceId = u16;
        \\pub fn nextSourceId(files: *const std.ArrayList([]const u8)) SourceId {
        \\    return @intCast(files.items.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const SourceId = u16;
        \\pub fn nextSourceId(files: *const std.ArrayList([]const u8)) !SourceId {
        \\    if (files.items.len > std.math.maxInt(SourceId)) return error.Full;
        \\    return @intCast(files.items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean unchecked duration counts remain unsafe" {
    try testing.expectFiresTyped(check, R,
        \\pub fn durationCount(durations: []const u64) u32 {
        \\    return @intCast(durations.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn durationCount(durations: []const u64) !u32 {
        \\    if (durations.len > std.math.maxInt(u32)) return error.Full;
        \\    return @intCast(durations.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: returned tagged union payloads keep fixed slice extents" {
    try testing.expectNoFireTyped(check,
        \\const Action = union(enum) { unchanged, replace: []const u32 };
        \\fn hook(scratch: *[2]u32) Action {
        \\    return .{ .replace = scratch[0..2] };
        \\}
        \\fn accepts(count: u16) bool { return count == 2; }
        \\pub fn inspect() bool {
        \\    var scratch = [2]u32{ 1, 2 };
        \\    const action = hook(&scratch);
        \\    switch (action) {
        \\        .unchanged => return false,
        \\        .replace => |inputs| return accepts(@intCast(inputs.len)),
        \\    }
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Action = union(enum) { unchanged, replace: []const u32 };
        \\fn hook(scratch: *[3]u32, short: bool) Action {
        \\    if (short) return .{ .replace = scratch[0..2] };
        \\    const action = Action{ .replace = scratch[0..3] };
        \\    const copy = action;
        \\    return copy;
        \\}
        \\pub fn inspect(short: bool) u16 {
        \\    var scratch = [3]u32{ 1, 2, 3 };
        \\    const action = hook(&scratch, short);
        \\    switch (action) {
        \\        .unchanged => return 0,
        \\        .replace => |inputs| return @intCast(inputs.len),
        \\    }
        \\}
    );
}

test "index-type-narrowing-wraparound: returned union lengths reject unknown oversized and other variants" {
    try testing.expectFiresTyped(check, R,
        \\const Action = union(enum) { unchanged, replace: []const u32 };
        \\fn hook(scratch: *[2]u32, unknown: []const u32, alternate: bool) Action {
        \\    if (alternate) return .{ .replace = unknown };
        \\    return .{ .replace = scratch[0..2] };
        \\}
        \\pub fn inspect(unknown: []const u32, alternate: bool) u16 {
        \\    var scratch = [2]u32{ 1, 2 };
        \\    const action = hook(&scratch, unknown, alternate);
        \\    switch (action) {
        \\        .unchanged => return 0,
        \\        .replace => |inputs| return @intCast(inputs.len),
        \\    }
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Action = union(enum) { unchanged, replace: []const u32 };
        \\fn hook(scratch: *[65536]u32, alternate: bool) Action {
        \\    if (alternate) return .{ .replace = scratch[0..65536] };
        \\    return .{ .replace = scratch[0..2] };
        \\}
        \\pub fn inspect(scratch: *[65536]u32, alternate: bool) u16 {
        \\    const action = hook(scratch, alternate);
        \\    switch (action) {
        \\        .unchanged => return 0,
        \\        .replace => |inputs| return @intCast(inputs.len),
        \\    }
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Action = union(enum) { replace: []const u32, append: []const u32 };
        \\fn hook(scratch: *[2]u32, unknown: []const u32, alternate: bool) Action {
        \\    if (alternate) return .{ .append = unknown };
        \\    return .{ .replace = scratch[0..2] };
        \\}
        \\pub fn inspect(unknown: []const u32, alternate: bool) u16 {
        \\    var scratch = [2]u32{ 1, 2 };
        \\    const action = hook(&scratch, unknown, alternate);
        \\    switch (action) {
        \\        .replace => return 0,
        \\        .append => |inputs| return @intCast(inputs.len),
        \\    }
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Action = union(enum) { unchanged, replace: []const u32 };
        \\fn hook(scratch: *[2]u32, alternate: bool) Action {
        \\    if (alternate) return .unchanged;
        \\    return .{ .replace = scratch[0..2] };
        \\}
        \\pub fn inspect(alternate: bool) u16 {
        \\    var scratch = [2]u32{ 1, 2 };
        \\    const action = hook(&scratch, alternate);
        \\    switch (action) {
        \\        .unchanged => return 0,
        \\        .replace => |inputs| return @intCast(inputs.len),
        \\    }
        \\}
    );
}

test "index-type-narrowing-wraparound: inferred fixed array modulo has a bounded result" {
    try testing.expectNoFireTyped(check,
        \\fn next(state: *u64) u64 {
        \\    state.* = state.* *% 3 +% 1;
        \\    return state.*;
        \\}
        \\pub fn choose(state: *u64) u8 {
        \\    const operations = [_]u8{ 1, 2, 3 };
        \\    return operations[@as(usize, @intCast(next(state) % operations.len))];
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn choose(raw: u64) u8 {
        \\    const operations = [_]u8{ 1, 2, 3 };
        \\    return @intCast(raw % operations.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn choose(raw: u64) u8 {
        \\    const operations: [257]u8 = undefined;
        \\    return @intCast(raw % operations.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn choose(raw: anytype) u8 {
        \\    const operations = [_]u8{ 1, 2, 3 };
        \\    return @intCast(raw % operations.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: opaque instruction imports retain conservative bounds" {
    try testing.expectFiresTyped(check, R,
        \\const Grammar = @import("spirv_grammar");
        \\pub fn encode(words: []const u32, arities: []u8) !void {
        \\    var cursor: usize = 0;
        \\    while (cursor < words.len) {
        \\        const instruction = Grammar.decodeInstruction(words, &cursor) catch {
        \\            return error.InvalidInput;
        \\        };
        \\        if (instruction.words.len < 3 or instruction.words.len > 9) {
        \\            return error.InvalidInput;
        \\        }
        \\        arities[0] = @intCast(instruction.words.len - 2);
        \\    }
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Instruction = struct { words: []const u32 };
        \\pub fn encode(instruction: Instruction, arities: []u8) !void {
        \\    if (instruction.words.len < 3 or instruction.words.len > 9) {
        \\        return error.InvalidInput;
        \\    }
        \\    arities[0] = @intCast(instruction.words.len - 2);
        \\}
    );
}

test "index-type-narrowing-wraparound: checked nonnegative totals bound each component" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u32 {
        \\    const total = std.math.add(usize, base, pending.len) catch return error.Full;
        \\    if (total > std.math.maxInt(u32)) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u8 {
        \\    const total = try std.math.add(usize, base, pending.len);
        \\    if (total > 255) return error.Full;
        \\    return @intCast(base);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u32 {
        \\    const total = std.math.add(usize, base, pending.len) catch {
        \\        return error.Full;
        \\    };
        \\    if (total > std.math.maxInt(u32)) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn checkCount(total: usize) !void {
        \\    if (total > 255) return error.Full;
        \\}
        \\pub fn count(base: usize, pending: []const u8) !u8 {
        \\    const total = try std.math.add(usize, base, pending.len);
        \\    try checkCount(total);
        \\    return @intCast(pending.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: checked total components reject fallback signed and overshoot proofs" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u8 {
        \\    const total = std.math.add(usize, base, pending.len) catch 0;
        \\    if (total > 255) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u8 {
        \\    const total = std.math.add(usize, base, pending.len) catch blk: {
        \\        break :blk 0;
        \\    };
        \\    if (total > 255) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn count(base: i64, pending: []const u8) !u32 {
        \\    if (pending.len > std.math.maxInt(i64)) return error.Full;
        \\    const total = try std.math.add(i64, base, @intCast(pending.len));
        \\    if (total > std.math.maxInt(u32)) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u8 {
        \\    const total = try std.math.add(usize, base, pending.len);
        \\    if (total > 255) return error.Full;
        \\    return @intCast(pending.len + 1);
        \\}
    );
}

test "index-type-narrowing-wraparound: component relations retire on rebind and alias writes" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8, replacement: []const u8) !u8 {
        \\    var input = pending;
        \\    const total = try std.math.add(usize, base, input.len);
        \\    input = replacement;
        \\    if (total > 255) return error.Full;
        \\    return @intCast(input.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn count(base: usize, pending: []const u8) !u8 {
        \\    var total = try std.math.add(usize, base, pending.len);
        \\    total = 0;
        \\    if (total > 255) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Holder = struct { items: []const u8 };
        \\pub fn count(base: usize, holder: *Holder, replacement: []const u8) !u8 {
        \\    const total = try std.math.add(usize, base, holder.items.len);
        \\    const alias = holder;
        \\    alias.items = replacement;
        \\    if (total > 255) return error.Full;
        \\    return @intCast(holder.items.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Holder = struct { items: []const u8 };
        \\extern fn replace(holder: *Holder) void;
        \\pub fn count(base: usize, holder: *Holder) !u8 {
        \\    const total = try std.math.add(usize, base, holder.items.len);
        \\    if (total > 255) return error.Full;
        \\    replace(holder);
        \\    return @intCast(holder.items.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: aggregate wrappers remain conservative without return relations" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checkedAdd(a: u64, b: u64) !u64 { return std.math.add(u64, a, b); }
        \\fn checkedU64(a: usize) !u64 { return std.math.cast(u64, a) orelse error.Overflow; }
        \\pub fn sectionIndex(sections: []const u8, relocation_count: u32) !u32 {
        \\    const total = try checkedAdd(try checkedAdd(5, try checkedU64(sections.len)), relocation_count);
        \\    if (total > std.math.maxInt(u16)) return error.TooMany;
        \\    return @intCast(1 + sections.len + relocation_count);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checkedAdd(a: u64, b: u64) !u64 { return std.math.add(u64, a, b); }
        \\pub fn count(base: u64, pending: []const u8) !u32 {
        \\    const total = checkedAdd(base, pending.len) catch 0;
        \\    if (total > std.math.maxInt(u32)) return error.Full;
        \\    return @intCast(pending.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: total preflight does not invent container loop progress" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn append(gpa: std.mem.Allocator, records: *std.ArrayList(u32), pending: []const u8) !void {
        \\    const total = std.math.add(usize, records.items.len, pending.len) catch return error.Full;
        \\    if (total > std.math.maxInt(u32)) return error.Full;
        \\    try records.ensureUnusedCapacity(gpa, pending.len);
        \\    for (pending) |_| {
        \\        const id: u32 = @intCast(records.items.len + 1);
        \\        records.appendAssumeCapacity(id);
        \\    }
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn append(gpa: std.mem.Allocator, records: *std.ArrayList(u32), pending: []const u8) !void {
        \\    const total = std.math.add(usize, records.items.len, pending.len) catch return error.Full;
        \\    if (total > std.math.maxInt(u32)) return error.Full;
        \\    try records.ensureUnusedCapacity(gpa, pending.len);
        \\    for (pending) |_| {
        \\        const id: u32 = @intCast(records.items.len + 1);
        \\        records.appendAssumeCapacity(id);
        \\        records.appendAssumeCapacity(id);
        \\    }
        \\}
    );
}

test "index-type-narrowing-wraparound: Ocean capacity calls preserve copied guards but not mutable headers" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const State = struct {
        \\    path_text: std.ArrayList([]const u8) = .empty,
        \\    paths: std.StringHashMapUnmanaged(u32) = .empty,
        \\    pub fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) !u32 {
        \\        const length = self.path_text.items.len;
        \\        if (length > std.math.maxInt(u32)) return error.Budget;
        \\        try self.path_text.ensureUnusedCapacity(gpa, 1);
        \\        try self.paths.ensureUnusedCapacity(gpa, 1);
        \\        const id: u32 = @intCast(length);
        \\        self.path_text.appendAssumeCapacity(path);
        \\        self.paths.putAssumeCapacity(path, id);
        \\        return id;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const State = struct {
        \\    path_text: std.ArrayList([]const u8) = .empty,
        \\    paths: std.StringHashMapUnmanaged(u32) = .empty,
        \\    pub fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) !u32 {
        \\        if (self.path_text.items.len > std.math.maxInt(u32)) return error.Budget;
        \\        try self.path_text.ensureUnusedCapacity(gpa, 1);
        \\        try self.paths.ensureUnusedCapacity(gpa, 1);
        \\        self.path_text.appendAssumeCapacity(path);
        \\        const id: u32 = @intCast(self.path_text.items.len);
        \\        self.paths.putAssumeCapacity(path, id);
        \\        return id;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = struct {
        \\    items: []const []const u8,
        \\    fn ensureUnusedCapacity(self: *List, replacement: []const []const u8) !void {
        \\        self.items = replacement;
        \\    }
        \\};
        \\const State = struct {
        \\    path_text: List,
        \\    pub fn intern(self: *State, replacement: []const []const u8) !u32 {
        \\        if (self.path_text.items.len > std.math.maxInt(u32)) return error.Budget;
        \\        try self.path_text.ensureUnusedCapacity(replacement);
        \\        return @intCast(self.path_text.items.len);
        \\    }
        \\};
    );
}

const allocatorCallbackMutationSource =
    \\const std = @import("std");
    \\const CallbackAllocator = struct {
    \\    watched: *std.ArrayList(u8),
    \\    backing: std.heap.FixedBufferAllocator,
    \\    fn allocator(self: *CallbackAllocator) std.mem.Allocator {
    \\        return .{ .ptr = self, .vtable = &.{
    \\            .alloc = allocate, .resize = resize, .remap = remap, .free = free,
    \\        } };
    \\    }
    \\    fn allocate(context: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
    \\        const self: *CallbackAllocator = @ptrCast(@alignCast(context));
    \\        std.debug.assert(self.watched.capacity >= 300);
    \\        self.watched.items = self.watched.items.ptr[0..300];
    \\        return self.backing.allocator().rawAlloc(len, alignment, ret_addr);
    \\    }
    \\    fn resize(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
    \\        const self: *CallbackAllocator = @ptrCast(@alignCast(context));
    \\        return self.backing.allocator().rawResize(memory, alignment, new_len, ret_addr);
    \\    }
    \\    fn remap(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    \\        const self: *CallbackAllocator = @ptrCast(@alignCast(context));
    \\        return self.backing.allocator().rawRemap(memory, alignment, new_len, ret_addr);
    \\    }
    \\    fn free(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
    \\        const self: *CallbackAllocator = @ptrCast(@alignCast(context));
    \\        self.backing.allocator().rawFree(memory, alignment, ret_addr);
    \\    }
    \\};
    \\
;

const allocatorSnapshotGuardSource =
    \\pub fn copiedLengthAfterAllocation(watched: *std.ArrayList(u8), gpa: std.mem.Allocator) !u8 {
    \\    const length = watched.items.len;
    \\    if (length > 255) return error.Overflow;
    \\    var sibling: std.ArrayList(u8) = .empty;
    \\    defer sibling.deinit(gpa);
    \\    try sibling.ensureUnusedCapacity(gpa, 1);
    \\    return @intCast(length);
    \\}
    \\
;

test "index-type-narrowing-wraparound: an allocator callback can change a guarded header but not its copied length" {
    try testing.expectFiresTyped(check, R, allocatorCallbackMutationSource ++
        \\pub fn currentLengthAfterAllocation(watched: *std.ArrayList(u8), gpa: std.mem.Allocator) !u8 {
        \\    if (watched.items.len > 255) return error.Overflow;
        \\    var sibling: std.ArrayList(u8) = .empty;
        \\    defer sibling.deinit(gpa);
        \\    try sibling.ensureUnusedCapacity(gpa, 1);
        \\    return @intCast(watched.items.len);
        \\}
        \\
    );
    try testing.expectNoFireTyped(check, allocatorCallbackMutationSource ++ allocatorSnapshotGuardSource);
}

test "index-type-narrowing-wraparound: full width integer domains widen without interval encoding" {
    try testing.expectNoFireTyped(check,
        \\const Header = struct { len: u128 };
        \\pub fn same(header: Header) u128 { return @intCast(header.len); }
        \\pub fn wide(header: Header) i129 { return @intCast(header.len); }
        \\pub fn length(bytes: []const u8) i128 { return @intCast(bytes.len); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Header = struct { len: u128 };
        \\pub fn signed(header: Header) i128 { return @intCast(header.len); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Header = struct { len: i128 };
        \\pub fn unsigned(header: Header) u128 { return @intCast(header.len); }
    );
}

test "index-type-narrowing-wraparound: capacity arguments retain identity widths" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Init = struct { ast: struct { fields: []const u32 } };
        \\pub fn capacity(allocator: std.mem.Allocator, init: Init) !void {
        \\    var items: std.ArrayList(u32) = .empty;
        \\    defer items.deinit(allocator);
        \\    try items.ensureTotalCapacity(allocator, @intCast(init.ast.fields.len));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn tokenEnd(tree: *const std.zig.Ast) std.zig.Ast.TokenIndex {
        \\    return @intCast(tree.tokens.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: signed length fields need nonnegative value evidence" {
    try testing.expectNoFireTyped(check,
        \\const Header = struct { len: i128 };
        \\pub fn count(header: Header) !u128 {
        \\    if (header.len < 0) return error.Negative;
        \\    return @intCast(header.len);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Header = struct { len: i64 };
        \\pub fn count(header: Header) u128 {
        \\    return @intCast(header.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: AST initializer lengths widen into numeric constructors" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Range = union(enum) {
        \\    unknown,
        \\    integer: i128,
        \\    fn constant(value: i128) Range { return .{ .integer = value }; }
        \\};
        \\pub fn count(tree: *const std.zig.Ast, node: std.zig.Ast.Node.Index) Range {
        \\    var buffer: [2]std.zig.Ast.Node.Index = undefined;
        \\    const array = tree.fullArrayInit(&buffer, node) orelse return .unknown;
        \\    return Range.constant(@intCast(array.ast.elements.len));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Range = union(enum) {
        \\    unknown,
        \\    integer: i16,
        \\    fn constant(value: i16) Range { return .{ .integer = value }; }
        \\};
        \\pub fn count(tree: *const std.zig.Ast, node: std.zig.Ast.Node.Index) Range {
        \\    var buffer: [2]std.zig.Ast.Node.Index = undefined;
        \\    const array = tree.fullArrayInit(&buffer, node) orelse return .unknown;
        \\    return Range.constant(@intCast(array.ast.elements.len));
        \\}
    );
}
