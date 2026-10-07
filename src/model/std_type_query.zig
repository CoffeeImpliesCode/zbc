//! Canonical "does this name mean the real standard library?".
//!
//! `std` is a NAME: `const std = @import("std")` binds it, and every
//! later `std` in that file names that import.  So the proof is a
//! declaration, read out of the scopes the source nests around the
//! use: every function and container body that covers it, innermost
//! first, then the file's own top-level declarations.  A container's
//! members are read from the AST; a function's own parameters and
//! locals come from the cache's bindings.
//!
//! The frames AROUND the use count as much as the one it is written
//! in.  A type factory is evaluated where it is written, so
//! `fn Factory() type { const api = @import("std").mem; return struct {
//! fn open(a: api.Allocator) void {} }; }` writes that member against
//! the factory's own `api`, and a name has to be read through the
//! frames in between to know which one it is.  Every hop of a chain
//! is read at the token that DECLARED it, and a parameter, a `var` and
//! a capture clause each shadow what is written outside them.
//!
//! `declaration` is the walk: what a type expression reaches inside
//! the library (`std.mem.Allocator` → `"mem"` / `"Allocator"`).
//! `isType` compares that answer against one pair, for a consumer with
//! one name to check.  `aliasInitializer` returns the value a `const`
//! was written with, for one that needs the type behind a name.
//!
//! Nothing here reads a file.  The library's own source is not in this
//! session's reach, so everything after the import is read as SPELLED:
//! `std.mem.Allocator` is inside the library because it is written
//! that way, not because this walk opened `std`.  A consumer that must
//! not be fooled by a spelling selects from names it knows exist, and
//! a path deeper than one namespace is refused rather than matched.
//!
//! Everything unreadable is refused rather than guessed: another
//! module, a name declared twice at file level, a scope this walk
//! cannot settle, out of memory, a chain over `max_alias_depth`, a
//! walk that spends `step_budget`.  A refusal is null, or false.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");
const file_cache_mod = @import("../cache/file_cache.zig");

const FileCache = file_cache_mod.FileCache;
const TokenIndex = tokens.TokenIndex;

/// The module `@import("…")` written in `[first, last]` names, or
/// null when that range is not exactly that call.  `first` is the
/// `@import` builtin and `last` its closing paren; the literal is
/// the one token between them, unquoted, borrowed from the
/// snapshot.  Anything else — a second argument, a bare
/// identifier, an unterminated string — is not read, because a
/// name this walk cannot read is no proof.
fn importModuleLiteral(tree: *const Ast, first: TokenIndex, last: TokenIndex) ?[]const u8 {
    if (first + 3 != last) return null;
    const tags = tree.tokens.items(.tag);
    if (tags[first] != .builtin or !std.mem.eql(u8, tree.tokenSlice(first), "@import")) return null;
    if (tags[first + 1] != .l_paren or tags[last] != .r_paren) return null;
    if (tags[first + 2] != .string_literal) return null;
    const literal = tree.tokenSlice(first + 2);
    if (literal.len < 2) return null;
    return literal[1 .. literal.len - 1];
}

/// The import that makes a name mean the standard library.
const std_import = "std";

/// Aliases one question may cross.  A chain deeper than this is not
/// one a person wrote, and a chain that never ends — two declarations
/// naming each other — stops here instead of recursing.
const max_alias_depth = 8;

/// Names one dotted path may spell.  A path written straight off the
/// import carries the library's own names, so the import itself spends
/// none of them.
const max_path_names = 8;

/// Steps one question may take: a token read, a name looked up in a
/// declaration scope, an alias hop, a token skipped inside one
/// argument group, and an AST node read while finding the scopes a
/// name is written in.  Every scan this walk runs is charged before it
/// runs or as it runs, so what a question costs is bounded by this
/// and by the size of the file it is asked about.  A walk that has
/// spent them found no proof.
const step_budget = 8192;

/// Container bodies one use may be written inside.  A nest deeper
/// than this is refused rather than read down to the outermost frame
/// alone, which would answer with a shadow an inner one may hold.
const container_frames = 4;

/// Functions one use may be written inside.  A nest deeper than this
/// is refused rather than read down to the outermost frame alone,
/// which would answer with a shadow an inner one may hold.
const function_frames = 4;

/// What a caller is willing to read as part of the type it is asking
/// about.  Both start off: a caller that has not asked for an
/// instantiation or a pointer is asking about the bare path.
pub const Policy = struct {
    /// The range may end in one argument group, as
    /// `std.ArrayList(u8)` does.  The group says what the container
    /// holds, not which container it is, and is stepped over.
    allow_type_call: bool = false,
    /// The range may open with `*`, `?`, `const` or `volatile`, as
    /// `*const std.mem.Allocator` does.  Nothing else is stepped
    /// over: a slice or an array of this type is a different type,
    /// and a question about a pointer does not answer it.
    allow_pointer: bool = false,
};

/// An inclusive token range of one source snapshot.
pub const Range = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// A name inside the standard library: the one namespace it is
/// spelled under, and the name itself.  Both are the SOURCE's own
/// spelling, borrowed from the snapshot, so holding one costs
/// nothing.  There are exactly three answers — both fields empty for
/// the import itself, which spells no name of its own (the `std`
/// identifier, or a bare `@import("std")` call), an empty `module` for
/// a name the library owns (`std.ArrayList`, and the same name written
/// `@import("std").ArrayList`), and a `module` for a name one
/// namespace down (`std.mem.Allocator`).  A deeper path is not one of
/// these, and `declaration` refuses it.
pub const Declaration = struct {
    module: []const u8,
    name: []const u8,
};

/// What the type expression in `[first..last]` provably reaches inside
/// the standard library, or null when this file does not say.
pub fn declaration(
    cache: *FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    policy: Policy,
) ?Declaration {
    // Token indices are positions in ONE snapshot.  A range from
    // another document is not a position in this cache's
    // declarations, and reading it as one would answer with whatever
    // this file happens to spell at those indices.
    if (tree != cache.tree) return null;
    var walk = Walk.init(cache, tree, policy);
    const names = walk.reach(first, last, first, .any, 0) orelse return null;
    return switch (names.len) {
        0 => .{ .module = "", .name = "" },
        1 => .{ .module = "", .name = tree.tokenSlice(names.tokens[0]) },
        2 => .{
            .module = tree.tokenSlice(names.tokens[0]),
            .name = tree.tokenSlice(names.tokens[1]),
        },
        // Deeper than one namespace is inside the library, but not at
        // a place any caller names, and answering it would offer a
        // name whose spelling this walk never joined in one place.
        else => null,
    };
}

/// Does the type expression in `[first..last]` provably name
/// `module`.`name` inside the standard library?  One walk, one
/// comparison: this is `declaration` asked for a single pair.
pub fn isType(
    cache: *FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    module: []const u8,
    name: []const u8,
    policy: Policy,
) bool {
    const found = declaration(cache, tree, first, last, policy) orelse return false;
    return std.mem.eql(u8, found.module, module) and std.mem.eql(u8, found.name, name);
}

/// The value the `const` bound to the name written at `identifier`
/// was initialized with, or null when this name has no readable
/// initializer here.
///
/// `identifier` is the token the question is asked at: a USE of the
/// name, or the name token of the declaration itself.  A local
/// shadowing another declaration gets its own value, and a name
/// nothing binds here gets null rather than some other declaration's.
/// A parameter, a `var` and a capture clause bind a name without
/// declaring a value this walk can read, and so does a `const`
/// written with a type and no value (`const X: T;`) — its value is
/// not in this file.
pub fn aliasInitializer(
    cache: *FileCache,
    tree: *const Ast,
    identifier: Ast.TokenIndex,
) ?Range {
    if (tree != cache.tree) return null;
    if (@as(usize, identifier) >= tree.tokens.len) return null;
    if (tree.tokenTag(identifier) != .identifier) return null;
    var walk = Walk.init(cache, tree, .{});
    return switch (walk.bind(tree.tokenSlice(identifier), identifier, .any) orelse return null) {
        .shadowed => null,
        .const_value => |declared| declared.range,
    };
}

/// Names in one source range, kept as the tokens that spell them:
/// either a range's own spelling or the path a chain of declarations
/// reaches.  Tokens, not slices, so a dotted path can be read back as
/// the source wrote it without copying a byte.
const Names = struct {
    tokens: [max_path_names]TokenIndex,
    len: usize,
};

/// A range as written, and whether it was written straight off an
/// `@import("std")` — which is the identity itself, not a name to be
/// followed.
const Written = struct {
    names: Names,
    off_import: bool,
};

/// A `const`'s value, and the token its name was DECLARED at: every
/// name inside the value is read there rather than at the use that led
/// here, so a shadow written between the two is not mistaken for the
/// declaration's own meaning.
const Declared = struct {
    range: Range,
    anchor: TokenIndex,
    /// Where the DECLARATION is written, which is what the next hop
    /// has to read.  A file-level declaration is written outside every
    /// body, so nothing can shadow a name inside its value but another
    /// file-level declaration — and saying so here is what keeps a
    /// chain of root aliases from paying a scope pass per hop.
    frames: Frames,
};

/// The scopes a name has to be looked for in, as far as the walk knows.
const Frames = enum {
    /// Everywhere the source nests around the token.
    any,
    /// The file's own top level and nothing else.
    root,
};

/// What a name written at a use is bound to.
const Bound = union(enum) {
    /// A `const` declaration, and the value it was written with.
    const_value: Declared,
    /// Bound by something that is not a declaration this walk can
    /// read: a parameter, a `var`, a capture clause.  It SHADOWS the
    /// file's own declaration of the name — which is why the name
    /// stops here instead of falling through to it — and settles
    /// nothing about the standard library.
    shadowed,
};

/// The scopes a use is written in: every function and container body
/// that covers it, in the order the source nests them.  A use written
/// inside a container that a type factory returns is evaluated against
/// that factory's own declarations, so the frames AROUND the nearest
/// function are read too.
const Scope = struct {
    /// Function and container bodies covering the use, innermost
    /// first — which is the order their first tokens run backwards.
    frames: Frame(function_frames + container_frames) = .{},
    /// How many of those are functions, and how many containers.  The
    /// two kinds are capped apart, because a use is refused once
    /// either nest is deeper than this walk reads.
    functions: u8 = 0,
    containers: u8 = 0,
};

/// Declarations covering a use, ordered by how deeply they nest.
fn Frame(comptime limit: usize) type {
    return struct {
        nodes: [limit]Ast.Node.Index = undefined,
        len: usize = 0,

        /// Add `node`, keeping the list innermost first.  False when
        /// the list is full: a nest deeper than this walk reads is
        /// REFUSED rather than truncated, because the outermost frame
        /// alone could answer with a shadow an inner one holds.
        fn insert(self: *@This(), tree: *const Ast, node: Ast.Node.Index) bool {
            if (self.len == limit) return false;
            const first = tree.firstToken(node);
            // One is written inside the one that holds it, so the
            // later first token is the inner frame.
            var i: usize = 0;
            while (i < self.len and tree.firstToken(self.nodes[i]) > first) : (i += 1) {}
            // The shift moves the tail RIGHT, into the source range,
            // so it is copied from its end: copying forwards would
            // read an element after overwriting it and duplicate the
            // frames behind this one.
            std.mem.copyBackwards(Ast.Node.Index, self.nodes[i + 1 .. self.len + 1], self.nodes[i..self.len]);
            self.nodes[i] = node;
            self.len += 1;
            return true;
        }
    };
}

/// What one frame declares under a name.
const Answer = union(enum) {
    /// The frame does not declare this name; the next frame may.
    absent,
    /// A `const`, and the value it was written with.
    found: Declared,
    /// Declared here by something this walk cannot read a value out
    /// of: a parameter, a `var`, a capture clause, or a `const`
    /// written with a type and no value.  It shadows what is written
    /// outside the frame and settles nothing about the library.
    shadowed,
};

/// Every frame answer is nullable, and null is NOT `.absent`: it means
/// this frame cannot say — a scope this walk could not read, out of
/// memory, or a budget spent.  Such a frame may still declare the
/// name, so the frame outside it must not answer in its place.
/// True for the container declarations, the frames whose declarations
/// are written as members rather than in a body.
fn isContainerTag(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .container_decl, .container_decl_trailing, .container_decl_two, .container_decl_two_trailing, .container_decl_arg, .container_decl_arg_trailing => true,
        else => false,
    };
}

/// One question's walk over one snapshot.
const Walk = struct {
    cache: *FileCache,
    tree: *const Ast,
    policy: Policy,
    left: u32,

    fn init(cache: *FileCache, tree: *const Ast, policy: Policy) Walk {
        return .{ .cache = cache, .tree = tree, .policy = policy, .left = step_budget };
    }

    fn step(self: *Walk) bool {
        return self.charge(1);
    }

    // Compare collection costs at their native width before narrowing the
    // cost that fits the remaining bounded counter.
    fn charge(self: *Walk, ticks: usize) bool {
        if (ticks > @as(usize, self.left)) return false;
        self.left -= @intCast(ticks);
        return true;
    }

    /// The `)` closing the `(` at `lp`.  The matcher walks the whole
    /// group, so the group's length is compared with what is left
    /// BEFORE it runs: a group bigger than the whole remaining budget
    /// is refused without being read, and one that fits is charged
    /// for what it read.
    fn matchParen(self: *Walk, lp: TokenIndex, last: TokenIndex) ?TokenIndex {
        if (last - lp > self.left) return null;
        const close = tokens.matchParen(self.tree.tokens.items(.tag), lp, last) orelse return null;
        if (!self.charge(close - lp)) return null;
        return close;
    }

    /// The names `[first..last]` reach inside the standard library.
    /// The range's own first name is read at `anchor`, and every hop
    /// after that at the token that declared it.
    fn reach(self: *Walk, first: TokenIndex, last: TokenIndex, anchor: TokenIndex, frames: Frames, depth: u8) ?Names {
        if (!self.step()) return null;
        if (first > last or @as(usize, last) >= self.tree.tokens.len) return null;
        if (depth > max_alias_depth) return null;
        const written = self.readNames(first, last) orelse return null;
        // A path spelled straight off `@import("std")` is written
        // AGAINST the library, so every name it carries is already the
        // answer and none of them is a name to be followed: dropping
        // the first would answer with the next name's spelling shifted
        // left, and `@import("std").mem.Allocator` would name
        // `Allocator` at the top level.  The bare call spelled no name
        // of its own and IS the identity.
        if (written.off_import) return written.names;
        var names = self.reachName(
            self.tree.tokenSlice(written.names.tokens[0]),
            anchor,
            frames,
            depth,
        ) orelse return null;
        var i: usize = 1;
        while (i < written.names.len) : (i += 1) {
            if (names.len == max_path_names) return null;
            names.tokens[names.len] = written.names.tokens[i];
            names.len += 1;
        }
        return names;
    }

    /// What the name `name`, written at `use_token`, names inside the
    /// standard library, followed through the `const` declarations it
    fn reachName(self: *Walk, name: []const u8, use_token: TokenIndex, frames: Frames, depth: u8) ?Names {
        if (depth > max_alias_depth) return null;
        return switch (self.bind(name, use_token, frames) orelse return null) {
            .shadowed => null,
            .const_value => |declared| self.reach(
                declared.range.first,
                declared.range.last,
                declared.anchor,
                declared.frames,
                depth + 1,
            ),
        };
    }

    /// The scopes a use at `use_token` is written in, or null when one
    /// of them cannot be read.
    ///
    /// Follow the syntax path containing the token. Sibling initializers
    /// and function bodies cannot enclose it, so their descendants are not
    /// part of this query's work. Read every function and container on that
    /// path, including factories outside the innermost function.
    ///
    /// Each inspected child spends a step. No recursion or temporary tree
    /// is needed: syntax children have disjoint source spans, so at most
    /// one child can contain the token.
    fn scopeAt(self: *Walk, use_token: TokenIndex) ?Scope {
        var scope: Scope = .{};
        const tree = self.tree;
        const Iterator = @import("type_engine").AstIterator;
        var children: Iterator = .{ .sub_range = .{
            .items = tree.nodeData(.root).extra_range,
        } };
        while (children.next(tree)) |node| {
            if (!self.step()) return null;
            if (use_token < tree.firstToken(node) or use_token > tree.lastToken(node)) continue;
            const tag = tree.nodeTag(node);
            const container = isContainerTag(tag);
            if (container or tag == .fn_decl) {
                if (container) {
                    if (scope.containers == container_frames) return null;
                    scope.containers += 1;
                } else {
                    if (scope.functions == function_frames) return null;
                    scope.functions += 1;
                }
                if (!scope.frames.insert(tree, node)) return null;
            }
            children = Iterator.init(tree, node);
        }
        return scope;
    }

    /// What the name `name`, written at `use_token`, is bound to, in
    /// the order the source nests the scopes that can declare it, and
    /// finally the file's own top-level declarations.  A frame that
    /// cannot say refuses the question instead of letting the next one
    /// answer it.
    ///
    /// The frames around the use matter as much as the one it is
    /// written in: `fn Factory() type { const api = @import("std").mem;
    /// return struct { fn open(a: api.Allocator) void {} }; }` writes
    /// that member against the factory's own `api`, and a type factory
    /// is evaluated where it is written, so the name must be read
    /// through the frames in between to know which one it is.
    ///
    /// `frames` is what the previous hop learned about where the name
    /// is written.  `.root` skips the scope pass entirely; anything
    /// else reads every frame the use sits in.
    fn bind(self: *Walk, name: []const u8, use_token: TokenIndex, frames: Frames) ?Bound {
        if (!self.step()) return null;
        // A declaration read at file level is written outside every
        // body, so the only thing that can bind a name inside its
        // value is another file-level declaration.  Saying so skips
        // the scope pass a hop would otherwise pay, and a chain of
        // root aliases stays a chain of lookups.
        if (frames == .root) return self.rootBinding(name);
        const tree = self.tree;
        const scope = self.scopeAt(use_token) orelse return null;
        for (scope.frames.nodes[0..scope.frames.len]) |frame| {
            const answer = if (isContainerTag(tree.nodeTag(frame)))
                self.memberBinding(frame, name)
            else
                self.localBinding(frame, name, use_token);
            switch (answer orelse return null) {
                .found => |declared| return .{ .const_value = declared },
                .shadowed => return .shadowed,
                .absent => {},
            }
        }
        return self.rootBinding(name);
    }

    /// What the function `fn_decl` declares under `name` for a use at
    /// `use_token`, or null when this frame cannot say.
    fn localBinding(
        self: *Walk,
        fn_decl: Ast.Node.Index,
        name: []const u8,
        use_token: TokenIndex,
    ) ?Answer {
        const tree = self.tree;
        const body = tokens.bodyOf(tree, fn_decl) orelse return null;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return null;
        // The bindings are the cache's, built once per body, so this
        // is a lookup and not a walk.  Failing to build them is not
        // the same as there being no local of this name, and the
        // declaration they might shadow is exactly what must not be
        // read past them — so this refuses rather than falls through.
        const bindings = self.cache.localBindings(proto, body) catch return null;
        // A use written in the BODY is answered by the cache's own
        // lookup — the one reader of these bindings everywhere else —
        // and the scan it runs is charged up front and whole, because
        // it is bounded by the bindings of this one body.
        if (use_token < tree.firstToken(body)) {
            // A use in the function's OWN HEADER — the type of one of
            // its parameters — is written above the body, where the
            // scope ranges the lookup above tests do not reach, so it
            // cannot see the parameters written there.  Only a
            // parameter is visible from outside a body, and
            // `fn f(comptime std: type, a: std.mem.Allocator) type`
            // names the CALLER's std there, not this file's import.
            if (!self.charge(bindings.items.len)) return null;
            for (bindings.items) |*candidate| {
                if (candidate.origin != .param) continue;
                if (candidate.name_token > use_token) continue;
                if (std.mem.eql(u8, candidate.name, name)) return .shadowed;
            }
            return .absent;
        }
        if (!self.charge(bindings.items.len)) return null;
        const binding = bindings.findAt(name, use_token) orelse return .absent;
        switch (binding.origin) {
            // A parameter is a value handed in and a capture is a
            // value taken per iteration: neither declares a value
            // this walk can read, and both still shadow everything
            // written outside.
            .param, .loop_capture => return .shadowed,
            else => {},
        }
        // A `var` can be written to after the question is asked, so
        // what it holds at the use is not what its initializer said.
        if (!binding.is_const) return .shadowed;
        return .{
            .found = .{
                .range = .{ .first = binding.rhs_first, .last = binding.rhs_last },
                .anchor = binding.name_token,
                // A local is written inside a body, so the scopes around
                // its value have to be read again.
                .frames = .any,
            },
        };
    }

    /// What `container` declares under the name `name`, or null when
    /// this frame cannot say: a budget spent, or a container whose
    /// members this walk cannot read.  Such a frame may still declare
    /// the name, so the frame outside it must not answer in its place.
    fn memberBinding(self: *Walk, container: Ast.Node.Index, name: []const u8) ?Answer {
        const tree = self.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const decl = tree.fullContainerDecl(&buffer, container) orelse return null;
        for (decl.ast.members) |member| {
            if (!self.step()) return null;
            const declared = tree.fullVarDecl(member) orelse continue;
            const name_token = declared.ast.mut_token + 1;
            if (tree.tokenTag(name_token) != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(name_token), name)) continue;
            // A `var` member can be written to after the question is
            // asked, and a `const` written with a type and no value has
            // its initializer somewhere else.
            if (tree.tokenTag(declared.ast.mut_token) != .keyword_const) return .shadowed;
            const initializer = declared.ast.init_node.unwrap() orelse return .shadowed;
            return .{
                .found = .{
                    .range = .{ .first = tree.firstToken(initializer), .last = tree.lastToken(initializer) },
                    .anchor = name_token,
                    // A member is written inside a body, so the scopes
                    // around its value have to be read again.
                    .frames = .any,
                },
            };
        }
        return .absent;
    }

    /// The file-level declaration of `name`.  A file-level `const`
    /// owns its name for the whole file, so a use in any function
    /// reaches it when no local does.  This is the cache's own root
    /// tier, and its refusals are this walk's: a name declared twice
    /// is dropped there, because neither declaration is a proof, and a
    /// table that cannot be built is an incomplete file rather than a
    /// file with no constants in it.
    fn rootBinding(self: *Walk, name: []const u8) ?Bound {
        if (!self.step()) return null;
        const initializer = (self.cache.fileConstInitializer(name) catch return null) orelse return null;
        const tree = self.tree;
        const first = tree.firstToken(initializer);
        return .{
            .const_value = .{
                .range = .{ .first = first, .last = tree.lastToken(initializer) },
                // A root declaration's value is written in this file's own
                // scope, so its names are read there.
                .anchor = first,
                .frames = .root,
            },
        };
    }

    /// The dotted name written in `[first..last]`: identifiers
    /// separated by periods, behind whatever qualifiers the policy
    /// allows, and — with `allow_type_call` — one argument group at
    /// the very end.  A range that does not end there is a shape this
    /// walk does not read.
    fn readNames(self: *Walk, first: TokenIndex, last: TokenIndex) ?Written {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var t = first;
        var is_import = false;
        // `@import("std")` and a path written straight off it name
        // the library from the literal itself.  The literal is read by
        // the one reader every caller uses, and any other module is
        // another library: a name this walk cannot read is no proof.
        if (first + 1 <= last and tags[first] == .builtin and tags[first + 1] == .l_paren and
            std.mem.eql(u8, tree.tokenSlice(first), "@import"))
        {
            const close = self.matchParen(first + 1, last) orelse return null;
            const module = importModuleLiteral(tree, first, close) orelse return null;
            if (!std.mem.eql(u8, module, std_import)) return null;
            if (close == last) {
                // The import alone spells no name, so there is nothing
                // to carry: the empty list is the import itself.
                return .{ .names = .{ .tokens = undefined, .len = 0 }, .off_import = true };
            }
            if (tags[close + 1] != .period) return null;
            t = close + 2;
            is_import = true;
        } else if (self.policy.allow_pointer) {
            t = self.skipQualifiers(t, last) orelse return null;
        }
        var written: Names = .{ .tokens = undefined, .len = 0 };
        while (true) {
            if (t > last or !self.step()) return null;
            if (tags[t] != .identifier) return null;
            if (written.len == max_path_names) return null;
            written.tokens[written.len] = t;
            written.len += 1;
            t += 1;
            if (t > last) return .{ .names = written, .off_import = is_import };
            if (tags[t] == .l_paren) {
                // ONE argument group, at the end of the expression:
                // `std.ArrayList(u8)` asks which container it names,
                // and what follows a group is a member of an
                // instantiation, which is not the container.
                if (!self.policy.allow_type_call) return null;
                const close = self.matchParen(t, last) orelse return null;
                if (close != last or close == t + 1) return null;
                return .{ .names = written, .off_import = is_import };
            }
            if (tags[t] != .period) return null;
            t += 1;
        }
    }

    /// `*`, `?`, `const` and `volatile` in front of a type.  The
    /// caller allows them explicitly; without the policy none are
    /// stepped over, so `*Allocator` is never read as `Allocator`.
    fn skipQualifiers(self: *Walk, first: TokenIndex, last: TokenIndex) ?TokenIndex {
        const tags = self.tree.tokens.items(.tag);
        var t = first;
        while (t <= last) : (t += 1) {
            if (!self.step()) return null;
            switch (tags[t]) {
                .asterisk, .question_mark, .keyword_const, .keyword_volatile => {},
                else => return t,
            }
        }
        return t;
    }
};

test "budget charges reject wide costs before narrowing" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "", .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var walk = Walk.init(&cache, &tree, .{});
    const remaining = walk.left;
    try std.testing.expect(!walk.charge(std.math.maxInt(usize)));
    try std.testing.expectEqual(remaining, walk.left);
    try std.testing.expect(!walk.charge(@as(usize, remaining) + 1));
    try std.testing.expectEqual(remaining, walk.left);
    try std.testing.expect(walk.charge(remaining));
    try std.testing.expectEqual(@as(u32, 0), walk.left);
    try std.testing.expect(walk.charge(0));
    try std.testing.expect(!walk.charge(1));
}
