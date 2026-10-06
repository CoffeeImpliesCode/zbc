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
            if (cache.intInfoOf(params[0])) |source| {
                if (value_range.NumericRange.integerType(source.bits, source.signed).fitsInteger(destination.bits, destination.signed)) proved = true;
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
            // Without a destination there is nothing to compare against, and
            // inventing one is the guess this rule never makes.  This is also
            // what keeps the widening that RESTORES a narrowed value back to
            // subscript width (`array[@intCast(narrow)]`) quiet without a
            // heuristic for recognising it: a subscript context is not a
            // destination this type engine resolves.  A cast that NARROWS
            // again is not skipped — it fails the range proof on its own.
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
            .start = Pos.fromTokenStart(tree, token),
            .end = Pos.fromTokenEnd(tree, tree.lastToken(node)),
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
    const type_node = indexed.coerced.get(node) orelse return null;
    return cache.intInfoOf(type_node);
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

    fn init(gpa: std.mem.Allocator) IndexedUses {
        return .{
            .gpa = gpa,
            .direct = .empty,
            .bound = .empty,
            .declarer = .empty,
            .bindings = .empty,
            .coerced = .empty,
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
        \\fn build() u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 64 * 1024 * 1024 };
        \\    return builder.store("a");
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
        \\fn capped() u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 0 };
        \\    builder.max_text_bytes = @as(usize, max_u32);
        \\    return builder.store("a");
        \\}
        \\fn uncapped() u32 {
        \\    var builder: Builder = .{ .max_text_bytes = 64 * 1024 * 1024 };
        \\    return builder.store("a");
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
