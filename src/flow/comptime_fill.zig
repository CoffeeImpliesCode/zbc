//! Comptime static-constant evaluation and lexical scope resolution for
//! the CFG lowering.
//!
//! This is the half of `cfg_builder.zig` that answers questions about
//! what a `const` NAME MEANS and how MANY things there are: which
//! declaration a reference resolves to, how long an array type written
//! `N` is, and whether two sites are talking about the same count.  It
//! is a self-contained static evaluator with its own scope resolver, its
//! own declaration index and its own bounded expression evaluator, and
//! it changes for reasons CFG construction has nothing to do with —
//! which is why it lives here rather than inside the lowering.
//!
//! ## The interface is data, not behaviour
//!
//! A [Resolver] is handed three CONCRETE things and asks them questions:
//! the file's `*const Ast`, the per-file `FileCache` for the one length
//! no amount of token reading can produce, and the lowering's local
//! table through [LocalMap].  There is no callback vtable and no
//! interface object: a new question is a new method that reads those
//! three, and a caller is a [Resolver] built from them.  The lowering
//! stays private — nothing here takes a `*Builder`, and nothing here
//! is told how to classify an expression or emit a statement.
//!
//! ## One index
//!
//! The declaration index ([Resolver.index]) is built once per [Resolver]
//! and owned by it.  It is the single answer to "which bindings does
//! this file have"; there is no second copy anywhere, and a lowering
//! that builds one [Resolver] has exactly one index to free.

const std = @import("std");
const Ast = std.zig.Ast;

const cfg_types = @import("cfg.zig");
const file_cache = @import("../cache/file_cache.zig");
const tokens = @import("../ast/tokens.zig");

const LocalId = cfg_types.LocalId;
const LocalInfo = cfg_types.LocalInfo;

// ── Source ranges ─────────────────────────────────────────

/// Inclusive token index range covering a source construct.
pub const TokenSpan = struct { first: Ast.TokenIndex, last: Ast.TokenIndex };

/// A `var|const <name>: <T> = <init>;` declaration, located from the
/// local's recorded declaration offset.  `name_tok` proves the
/// declaration precedes a construct that writes through the binding;
/// `init_is_undefined` records the seed the initializer gave it.
pub const DeclTypeSpan = struct {
    type: TokenSpan,
    name_tok: Ast.TokenIndex,
    is_const: bool,
    init_is_undefined: bool,
    /// Token span of the initializer, when there IS one.  A
    /// declaration with no `=` has none; a proof that needs to read
    /// the seed (`var at: usize = 0;`) needs this rather than the
    /// boolean, because "seeded with the literal zero" and "seeded
    /// with something else" are the same question only this answers.
    init: ?TokenSpan = null,
};

/// A `const <name> = <init>;` declaration the scope resolver picked for
/// a reference: its optional type annotation and its initializer span.
/// It is a declaration now, not a name — [ScopedDecl.name_tok] says
/// WHICH `const` this is, and only that one's spans are here.
pub const FileConstDecl = struct {
    type: ?TokenSpan,
    init: TokenSpan,
};

// ── Extents ───────────────────────────────────────────────

/// How many elements a proof-side aggregate has, when the source
/// states that exactly.  Each field is a different way of stating
/// a COUNT, and [extentsAgree] is always agreement about a count
/// — never about a spelling:
///
///   - `number`: an element count both sides independently
///     resolved;
///   - `vec`: the immutable DECLARATION whose own length is the
///     count.  A target typed `T = @Tuple(&V)` has exactly `V.len`
///     fields and an enumeration over `V` walks exactly that many,
///     so the two agree when their `V`s are the same declaration —
///     which is why this carries the declaring NAME TOKEN rather
///     than the name's text;
///   - `collection`: a COMPILER REFLECTION collection whose `.len`
///     IS this extent.  A target declared `[func_info.params.len]`
///     holds `func_info.params.len` elements and
///     `for (func_info.params, 0..)` writes exactly that many, so
///     agreement is settled by both sites naming the same declared
///     collection — which is what [CollectionId] compares.  A
///     collection built out of storage states its count directly,
///     and that count is resolved by `number`.
pub const Extent = struct {
    number: ?u64 = null,
    vec: ?Ast.TokenIndex = null,
    collection: ?CollectionId = null,
};

/// Longest field path one length expression may walk.  A `.len`
/// read off a hand-built descriptor is a handful of steps; a
/// longer chain is a data structure, not a static extent.
const max_fill_path_fields = 8;

/// A field path over the immutable binding a length expression is
/// rooted in: that binding's already-resolved declaration, plus
/// the field names walked from it, in order.
const FieldPath = struct {
    root: ScopedDecl,
    fields: [max_fill_path_fields][]const u8,
    field_count: u8,
};

/// A COMPILER REFLECTION collection whose `.len` a `[<expr>.len]E`
/// target measures: the DECLARING name token of the binding the
/// expression is rooted in, plus the field path walked from it.
///
/// A declaration and its enumeration are necessarily DISJOINT token
/// ranges — `var types: [func_info.params.len]type` and
/// `for (func_info.params, 0..)` cannot be one span — so identity
/// has to come from what the two sites RESOLVE TO, not from where
/// they are written.  `root` is the declaring token, so this
/// `info` and another descriptor of the same shape resolve apart
/// even though they share a spelling; the path is compared by
/// field name, so `first.params` and `second.params` — two
/// descriptors that may even agree on how many parameters each has
/// — still resolve apart.
///
/// Only a reflection value may be identified this way.  Its count
/// is a property of the type it describes rather than of storage
/// anyone can write, which is what makes naming the same value at
/// both sites enough — see [Resolver.bindingHoldsReflectionValue].  A
/// collection built out of storage states its count directly, and
/// that count is resolved rather than matched.
pub const CollectionId = struct {
    root: Ast.TokenIndex,
    fields: [max_fill_path_fields][]const u8,
    field_count: u8,

    fn eql(a: CollectionId, b: CollectionId) bool {
        if (a.root != b.root or a.field_count != b.field_count) return false;
        for (a.fields[0..a.field_count], b.fields[0..b.field_count]) |mine, theirs| {
            if (!std.mem.eql(u8, mine, theirs)) return false;
        }
        return true;
    }
};

/// Do two aggregate extents state the same element count?  Every
/// branch is a claim about a count.  None is a claim that two
/// sources happen to be spelled alike, and none is a claim that a
/// side which simply failed to resolve matches anything.
pub fn extentsAgree(a: Extent, b: Extent) bool {
    if (a.number) |n| {
        if (b.number) |m| {
            if (n == m) return true;
        }
    }
    if (a.vec) |mine| {
        if (b.vec) |theirs| {
            if (mine == theirs) return true;
        }
    }
    if (a.collection) |mine| {
        if (b.collection) |theirs| {
            // Same declared reflection value, same field path —
            // one `.len`, read from two places that cannot share a
            // token range.
            if (mine.eql(theirs)) return true;
        }
    }
    return false;
}

// ── Declarations and scopes ───────────────────────────────

/// A binding a reference can see, with the scope it sits in.
pub const ScopedDecl = struct {
    /// Token index of the DECLARING name token — a declaration's
    /// identity.  Two proofs that resolve this token talk about the
    /// same declaration; two that merely share a spelling resolve
    /// different tokens.
    name_tok: Ast.TokenIndex,
    /// How many `{` enclose the declaration.  A reference sees the
    /// innermost — the largest — such count, so a `const` in an
    /// inner block beats one at file scope exactly as Zig's lookup
    /// does.
    scope_len: usize,
    /// Type-annotation and initializer spans, present only for a
    /// plain `const <name>[: T] = <init>;`.  A `var`, a parameter,
    /// a capture, a destructured name, and a `const` written some
    /// other way all carry null, which is what makes them unusable
    /// as the immutable anchor of a count.
    spans: ?FileConstDecl,
};

/// Running answer while the resolver scans for one name.
const DeclFind = struct {
    best: ?ScopedDecl = null,
    ambiguous: bool = false,

    fn add(self: *DeclFind, candidate: ScopedDecl) void {
        if (self.best) |held| {
            // An outer declaration loses to an inner one, and two
            // in the SAME scope is a tie nothing here can break.
            if (held.scope_len > candidate.scope_len) return;
            if (held.scope_len == candidate.scope_len) {
                self.ambiguous = true;
                return;
            }
        }
        self.best = candidate;
        self.ambiguous = false;
    }
};

/// One binding this file creates: a `const`/`var` name, or a name a
/// `| a, b |` payload binds.
pub const Declaration = struct {
    /// Token of the DECLARING name token.  A declaration's identity.
    name_tok: Ast.TokenIndex,
    /// How many `{` enclosed it when it was written.  File scope is
    /// zero.
    scope_len: usize,
    /// The innermost of those `{`; meaningless at file scope, where
    /// `scope_len` is zero.  One token identifies the whole chain: a
    /// `{` has exactly one enclosing chain, so equality at the
    /// innermost level forces equality at every outer one.
    ///
    /// Not read outside this module: comparing the enclosing CHAIN is
    /// the visibility question, and [Resolver.visibleDeclAt] is the
    /// only thing that asks it.
    scope_brace: Ast.TokenIndex,
    kind: Kind,

    pub const Kind = enum { const_decl, var_decl, payload };
};

/// The declarations and prototype parameters [Resolver.visibleDeclAt]
/// answers from, read once per FileCache tree (or standalone resolver).
///
/// The question is asked repeatedly and always about the same
/// immutable tree: a `const` chain chased to its value asks it
/// once per link, and one fill proof asks the same binding from
/// the loop input, the target and the declared extent.  Each
/// question used to walk every token of the file and then every
/// AST node looking for a prototype enclosing the reference — so
/// one proof cost several whole-file passes, and a chain six deep.
///
/// What is stored is the RAW MATERIAL, not an answer: a binding's
/// own name token, the brace depth it sat at, and which of the
/// three kinds of binding it is.  [parseConstDeclAt] still runs at
/// query time for the entries whose name matches, so a file with
/// many constants never parses one a question did not ask about.
/// Visibility, shadowing and the capture / `var` / `const`
/// distinctions are therefore still decided by
/// [Resolver.visibleDeclAt] exactly as before — only how often the
/// file is read to find the candidates changes.
pub const LexicalIndex = struct {
    /// Every `const`/`var` name token and every name a `| a, b |`
    /// payload binds, in source order.
    decls: std.ArrayListUnmanaged(Declaration) = .empty,
    /// Every prototype parameter in the file, with the body range
    /// it binds inside.
    params: std.ArrayListUnmanaged(ParamEntry) = .empty,
    /// Exact syntax-only answers. The owning index supplies tree identity.
    visible: std.HashMapUnmanaged(VisibleKey, ?ScopedDecl, VisibleContext, 80) = .empty,

    /// Set once the walk has run, so a build that gave up is not
    /// retried — and re-failed — by every later question.
    built: bool = false,
    /// False when the walk stopped early: the fixed brace buffer
    /// ran out, or an append failed.  A question against an
    /// incomplete index is DECLINED, because a binding the walk
    /// never reached is not evidence that none exists.
    complete: bool = true,

    const VisibleKey = struct {
        token: Ast.TokenIndex,
        name: []const u8,
        owned_name: bool = false,
    };

    const VisibleContext = struct {
        pub fn hash(_: VisibleContext, key: VisibleKey) u64 {
            return std.hash.Wyhash.hash(key.token, key.name);
        }

        pub fn eql(_: VisibleContext, a: VisibleKey, b: VisibleKey) bool {
            return a.token == b.token and std.mem.eql(u8, a.name, b.name);
        }
    };
    const ParamEntry = struct {
        name_tok: Ast.TokenIndex,
        name: []const u8,
        body_first: Ast.TokenIndex,
        body_last: Ast.TokenIndex,
    };

    pub fn deinit(self: *LexicalIndex, gpa: std.mem.Allocator) void {
        self.decls.deinit(gpa);
        self.params.deinit(gpa);
        var keys = self.visible.keyIterator();
        while (keys.next()) |key| if (key.owned_name) gpa.free(key.name);
        self.visible.deinit(gpa);
    }
};

/// Deepest brace nesting the scope resolver will track for a fill
/// proof.  A reference nested past this declines rather than
/// guessing which block its name came from.
const max_fill_scope_depth = 64;

/// Ceilings on how far a comptime length expression may be chased
/// through `const` initializers, and on how many tokens one
/// expression may span.  Each level costs one file scan, so both
/// bound the work an `inline for` in a big file can ask for.
const max_fill_eval_depth = 6;
const max_fill_eval_tokens = 32;

/// How many identifiers and commas one `| a, b |` payload run may
/// list.  A longer run is not a payload.  One bound for both the
/// index that collects them and every query that reads it.
const capture_scan_limit = 8;

// ── The lowering's local table, seen from here ─────────────

/// The two tables a lowering already keeps, named by what they are.
///
/// Both are passed as POINTERS because both grow while the lowering
/// runs: a local declared later is registered later, and a scope
/// question asked about the middle of a body has to see the bindings
/// that existed there.  The pointers are to the STORAGE, not to a
/// snapshot, so a resolver bound once keeps answering about the
/// current table without being told again.
pub const LocalMap = struct {
    /// name → LocalId, exactly the lowering's current-scope table.
    by_name: *const std.StringHashMapUnmanaged(LocalId),
    /// The registered locals, indexed by LocalId.  Carries the name
    /// and the declaration offset this resolver matches prototypes
    /// and annotations against.
    info: *const std.ArrayListUnmanaged(LocalInfo),

    /// The local a name is bound to in the current scope, or null
    /// when nothing in this scope binds it.
    pub fn localOf(self: LocalMap, name: []const u8) ?LocalId {
        return self.by_name.get(name);
    }
};

// ── Resolver ──────────────────────────────────────────────

pub const Resolver = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    /// The per-file FileCache, for the one question tokens cannot
    /// answer: the compile-time length of an array type whose `N` was
    /// written in another module (`[Sha256.digest_length]u8`).  Null
    /// when the lowering runs without one, and the question then
    /// declines rather than guessing.
    cache: ?*file_cache.FileCache,
    /// Prototype of the ONE function this resolver answers for, and
    /// null for a resolver built outside a function lowering.  It is
    /// the only place a parameter name or a `comptime T: type`
    /// binding is created.
    fn_proto: ?Ast.full.FnProto,
    /// The lowering's local table, null until [Resolver.bindLocals].
    locals: ?LocalMap = null,
    /// Fallback index for standalone resolvers or a foreign tree. Matching
    /// FileCache trees own the shared index across lowerings and replays.
    lex: LexicalIndex = .{},

    /// A resolver that answers about `tree` for the single function
    /// `fn_proto` describes.  [Resolver.bindLocals] must follow,
    /// before any question — see [Resolver.locals].
    pub fn init(
        gpa: std.mem.Allocator,
        tree: *const Ast,
        cache: ?*file_cache.FileCache,
        fn_proto: ?Ast.full.FnProto,
    ) Resolver {
        return .{ .gpa = gpa, .tree = tree, .cache = cache, .fn_proto = fn_proto };
    }

    /// Point the resolver at the local table it is to answer about.
    ///
    /// This is separate from [Resolver.init] because the table belongs
    /// to the lowering that owns the resolver, so the lowering has to
    /// exist before there is anything to point at.  The pointers are
    /// to that lowering's storage and stay valid for as long as it
    /// does.
    pub fn bindLocals(
        self: *Resolver,
        by_name: *const std.StringHashMapUnmanaged(LocalId),
        info: *const std.ArrayListUnmanaged(LocalInfo),
    ) void {
        self.locals = .{ .by_name = by_name, .info = info };
    }

    pub fn deinit(self: *Resolver) void {
        self.lex.deinit(self.gpa);
        self.lex = .{};
    }

    // ── Declarations ────────────────────────────────────────

    /// Token span of the type annotation in `var|const <name>: <T> =
    /// <init>`, together with whether the binding is `const` and
    /// whether the initializer was the `undefined` keyword.  Null for
    /// every shape we don't model exactly: a parameter, an
    /// `align`/`address`/`section` modifier that would fold extra
    /// tokens into the span, or a declaration we can't attribute.
    ///
    /// A PARAMETER is null here by construction — the token before
    /// its name is a paren or a comma, not `var`/`const` — and
    /// [Resolver.declaredTypeSpanOfLocal] reaches those separately,
    /// because "the declared type of this local" is one question and
    /// a parameter's is one of the two ways to answer it.
    pub fn declaredTypeSpanOfLocal(self: *const Resolver, local: LocalId) ?DeclTypeSpan {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const starts = tree.tokens.items(.start);
        const locals = self.locals orelse return null;
        if (@intFromEnum(local) >= locals.info.items.len) return null;
        const info = locals.info.items[@intFromEnum(local)];
        // decl_pos is the byte offset of the declaring name token;
        // find the last token starting at or before it.
        var lo: usize = 0;
        var hi: usize = starts.len;
        while (lo < hi) {
            const mid = lo + (hi - lo) / 2;
            if (starts[mid] <= info.decl_pos.byte) lo = mid + 1 else hi = mid;
        }
        if (lo == 0) return null;
        // The search answers a position in `starts`, so the token index
        // is inside the list by construction — the lowering entry point
        // bounds that list by the source width.  Narrowing is still
        // CHECKED rather than assumed: a `@intCast` here would trap in
        // Debug/ReleaseSafe if that bound were ever broken, and this
        // function's own contract is that a shape it cannot place
        // returns null rather than aborting the lowering.
        const name_tok = std.math.cast(Ast.TokenIndex, lo - 1) orelse return null;
        if (tags[name_tok] != .identifier) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(name_tok), info.name)) return null;
        if (name_tok == 0) return null;
        const is_const = switch (tags[name_tok - 1]) {
            .keyword_var => false,
            .keyword_const => true,
            else => return null,
        };
        if (name_tok + 1 >= tags.len or tags[name_tok + 1] != .colon) return null;
        const first = name_tok + 2;
        var depth: u32 = 0;
        var t = first;
        while (t < tags.len) : (t += 1) {
            const tag = tags[t];
            if (depth == 0 and (tag == .equal or tag == .semicolon or tag == .comma)) {
                if (t == first) return null;
                return .{
                    .type = .{ .first = first, .last = t - 1 },
                    .name_tok = name_tok,
                    .is_const = is_const,
                    .init_is_undefined = tag == .equal and t + 1 < tags.len and
                        tags[t + 1] == .identifier and
                        std.mem.eql(u8, tree.tokenSlice(t + 1), "undefined"),
                    .init = if (tag == .equal) initSpanAfter(tree, t) else null,
                };
            }
            switch (tag) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => {
                    if (depth == 0) return null;
                    depth -= 1;
                },
                else => {},
            }
        }
        return null;
    }

    /// Every declaration and capture name the index recorded, or null
    /// when the walk gave up.
    ///
    /// Null is the honest answer rather than an empty list: a binding
    /// the walk never reached is not a binding that is not there, and
    /// a caller about to REGISTER locals from this list must not
    /// conclude the file has none.
    pub fn declarations(self: *const Resolver) ?[]const Declaration {
        const lex = self.index();
        if (!lex.complete) return null;
        return lex.decls.items;
    }

    /// The immutable `const` declaration a bare identifier reference at
    /// `use_tok` names — or null when nothing is visible, when what is
    /// visible is a `var`, a parameter, a capture or a destructured
    /// name, or when two declarations tie for the name.
    ///
    /// This is a scope question, not a spelling question.  The
    /// file-wide `const <name>` search it replaces could read a
    /// declaration out of a sibling namespace, so an unrelated
    /// `const specs` of length three could vouch for a fill over some
    /// other `specs` of length two, and the tail of that fill would
    /// read as defined.
    pub fn visibleConstDecl(self: *const Resolver, use_tok: Ast.TokenIndex, name: []const u8) ?ScopedDecl {
        const decl = self.visibleDeclAt(use_tok, name) orelse return null;
        if (decl.spans == null) return null;
        return decl;
    }

    /// Every declaration that binds `name` at `use_tok`, resolved
    /// through the file's real scopes and reduced to the innermost.
    ///
    /// Visibility is the enclosing-brace chain: a declaration is seen
    /// exactly when every block it sits in also encloses the reference.
    /// That one rule answers for a block, a container body and a
    /// sibling block alike, because each opens a brace — which is what
    /// keeps a `const` inside one container from answering for a
    /// reference inside another.  Where the chain alone is too coarse
    /// (a capture really only reaches its own body) the scan claims
    /// MORE visibility than exists: claiming a binding that is not
    /// there costs a declined proof, while missing one that is would
    /// let a shadowed name vouch for a count.
    ///
    /// Candidates come from the index, not from a walk: this question
    /// is asked once per link of a `const` chain and several times per
    /// fill proof, and each asking used to read the whole file twice
    /// over.  The index stores only what a binding IS — where it was
    /// written, under which braces, of which kind — so every decision
    /// made here about visibility, shadowing and kind is made from
    /// the same inputs, exactly as it was when read straight off the
    /// tokens.
    ///
    /// A `var`/`const` the reference cannot see is `foreign`, and one
    /// `foreign` name declines the whole question.  A payload that
    /// does not reach is not `foreign`, because a capture's real
    /// reach was already being claimed wider than it exists and the
    /// scan never treated a missing capture as evidence of anything.
    pub fn visibleDeclAt(self: *const Resolver, use_tok: Ast.TokenIndex, name: []const u8) ?ScopedDecl {
        if (use_tok >= self.tree.tokens.len) return null;
        const lex = self.index();
        if (!lex.complete) return null;
        const key: LexicalIndex.VisibleKey = .{ .token = use_tok, .name = name };
        if (lex.visible.getPtr(key)) |answer| return answer.*;
        const answer = self.visibleDeclAtUncached(use_tok, name);
        const gpa = self.indexAllocator();
        var saved = key;
        if (answer) |decl| {
            saved.name = self.tree.tokenSlice(decl.name_tok);
        } else if (std.mem.eql(u8, self.tree.tokenSlice(use_tok), name)) {
            saved.name = self.tree.tokenSlice(use_tok);
        } else {
            saved.name = gpa.dupe(u8, name) catch return answer;
            saved.owned_name = true;
        }
        lex.visible.put(gpa, saved, answer) catch {
            if (saved.owned_name) gpa.free(saved.name);
        };
        return answer;
    }

    fn visibleDeclAtUncached(self: *const Resolver, use_tok: Ast.TokenIndex, name: []const u8) ?ScopedDecl {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (use_tok >= tags.len) return null;

        var regions: [max_fill_scope_depth]Ast.TokenIndex = undefined;
        const region_len = openBraceStack(tags, use_tok, &regions) orelse return null;

        const lex = self.index();
        // An index that stopped early answers nothing: a binding the
        // walk never reached is not a binding that is not there.
        if (!lex.complete) return null;

        var found: DeclFind = .{};
        // A name this file declares more than once is not one this
        // analysis will count on, even when the scope chain settles
        // which declaration a reference means: the point of resolving
        // visibility is to never answer from a declaration the
        // reference does not name, and a second declaration under the
        // same spelling is the case where a count read off the wrong
        // one is hardest to see.  It costs a declined proof, never a
        // wrong one.
        var foreign = false;
        for (lex.decls.items) |entry| {
            // Zig declares before it uses: a name that does not yet
            // exist at `use_tok` is not the binding this reference
            // names.  Only the FIRST declaring token matters — a later
            // `var x = …;` re-statement of a name already in scope is
            // not a new declaration, and it is the earlier one the
            // reference resolves to.
            if (entry.name_tok >= use_tok) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(entry.name_tok), name)) continue;
            // Every brace enclosing the binding encloses the
            // reference.  Comparing the innermost one is enough: a `{`
            // has exactly one enclosing chain, so equality there
            // forces equality at every outer level.
            const in_scope = entry.scope_len <= region_len and
                (entry.scope_len == 0 or regions[entry.scope_len - 1] == entry.scope_brace);
            if (in_scope) {
                found.add(.{
                    .name_tok = entry.name_tok,
                    .scope_len = entry.scope_len,
                    .spans = if (entry.kind == .const_decl) parseConstDeclAt(tree, entry.name_tok) else null,
                });
            } else if (entry.kind != .payload) {
                foreign = true;
            }
        }

        // A parameter binds inside its own fn's body and nowhere else,
        // so its scope is the enclosing chain plus the body's brace.
        // The prototype is the only place a parameter name is created,
        // and the iteration reaches nested fns — a struct literal's
        // method reads the locals of the fn that built the literal,
        // which is how a generated wrapper's `args_tuple` / `arg_types`
        // pair reaches the loop that fills it.
        for (lex.params.items) |entry| {
            if (use_tok < entry.body_first or use_tok > entry.body_last) continue;
            if (!std.mem.eql(u8, entry.name, name)) continue;
            var body_index: usize = 0;
            var in_body = false;
            while (body_index < region_len) : (body_index += 1) {
                if (regions[body_index] != entry.body_first) continue;
                in_body = true;
                break;
            }
            if (!in_body) continue;
            found.add(.{ .name_tok = entry.name_tok, .scope_len = body_index + 1, .spans = null });
        }

        if (found.ambiguous or foreign) return null;
        return found.best;
    }

    fn indexAllocator(self: *const Resolver) std.mem.Allocator {
        if (self.cache) |cache| if (cache.tree == self.tree) return cache.gpa;
        return self.gpa;
    }

    /// Build syntax-only raw material once for the matching cache tree.
    /// Standalone/foreign resolvers own their fallback. An incomplete walk
    /// still declines every query, including a previously memoized answer.
    fn index(self: *const Resolver) *LexicalIndex {
        const lex: *LexicalIndex = if (self.cache) |cache|
            if (cache.tree == self.tree) &cache.fill_lexical_index else @constCast(&self.lex)
        else
            @constCast(&self.lex);
        if (lex.built) return lex;
        lex.built = true;
        const gpa = self.indexAllocator();
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);

        var stack: [max_fill_scope_depth]Ast.TokenIndex = undefined;
        var depth: usize = 0;
        var t: Ast.TokenIndex = 0;
        while (t < tags.len) : (t += 1) {
            // The braces enclosing whatever this token binds, read
            // once here so all three binding arms record the same
            // scope the old in-line scan measured at this point.
            const scope_len = depth;
            const scope_brace: Ast.TokenIndex = if (depth == 0) 0 else stack[depth - 1];
            switch (tags[t]) {
                .l_brace => {
                    if (depth == max_fill_scope_depth) {
                        lex.complete = false;
                        break;
                    }
                    stack[depth] = t;
                    depth += 1;
                },
                .r_brace => {
                    if (depth > 0) depth -= 1;
                },
                .keyword_const, .keyword_var => {
                    // Every modifier (`pub`, `comptime`, `export`,
                    // `inline`, `threadlocal`) sits BEFORE the keyword,
                    // so the bound name is always the token after it.
                    const name_tok: Ast.TokenIndex = t + 1;
                    // A keyword with no name after it binds nothing, and
                    // it can only be the file's last token — a source
                    // ending there does not parse.  Skipping it keeps
                    // the index whole rather than truncating it behind
                    // a complete index's claim.
                    if (name_tok >= tags.len) continue;
                    if (tags[name_tok] != .identifier) continue;
                    lex.decls.append(gpa, .{
                        .name_tok = name_tok,
                        .scope_len = scope_len,
                        .scope_brace = scope_brace,
                        .kind = if (tags[t] == .keyword_const) .const_decl else .var_decl,
                    }) catch {
                        lex.complete = false;
                        break;
                    };
                },
                .pipe => {
                    // `| a |`, `| a, b |`, `| *a |`: a payload binds
                    // every name it lists.  A binary `a | b` reads as
                    // one too, which only invents a binding — the safe
                    // direction.
                    var u: Ast.TokenIndex = t + 1;
                    var want_name = true;
                    var steps: usize = 0;
                    while (u < tags.len and steps < capture_scan_limit) : (steps += 1) {
                        switch (tags[u]) {
                            .asterisk, .keyword_noalias => u += 1,
                            .comma => {
                                u += 1;
                                want_name = true;
                            },
                            .identifier => {
                                if (want_name) lex.decls.append(gpa, .{
                                    .name_tok = u,
                                    .scope_len = scope_len,
                                    .scope_brace = scope_brace,
                                    .kind = .payload,
                                }) catch {
                                    lex.complete = false;
                                    return lex;
                                };
                                u += 1;
                                want_name = false;
                            },
                            else => break,
                        }
                    }
                },
                else => {},
            }
        }

        var proto_buf: [1]Ast.Node.Index = undefined;
        var fns = tokens.iterFnDecls(tree);
        while (fns.next(&proto_buf)) |fn_entry| {
            const body_first = tree.firstToken(fn_entry.body);
            const body_last = tree.lastToken(fn_entry.body);
            var it = fn_entry.proto.iterate(tree);
            while (it.next()) |param| {
                const param_tok = param.name_token orelse continue;
                lex.params.append(gpa, .{
                    .name_tok = param_tok,
                    .name = tree.tokenSlice(param_tok),
                    .body_first = body_first,
                    .body_last = body_last,
                }) catch {
                    lex.complete = false;
                    return lex;
                };
            }
        }
        return lex;
    }

    // ── Comptime blocks and parameters ──────────────────────

    /// The `{` of the innermost `comptime` block — `comptime { … }` or
    /// `comptime label: { … }` — enclosing `tok`, or null when there
    /// is none.  Every statement of such a block is evaluated at
    /// comptime, so a `for` inside one walks its whole collection
    /// whether or not it is `inline`.
    pub fn comptimeBlockEnclosing(self: *const Resolver, tok: Ast.TokenIndex) ?Ast.TokenIndex {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var regions: [max_fill_scope_depth]Ast.TokenIndex = undefined;
        const region_len = openBraceStack(tags, tok, &regions) orelse return null;
        var i = region_len;
        while (i > 0) {
            i -= 1;
            const brace = regions[i];
            if (brace == 0) continue;
            if (tags[brace - 1] == .keyword_comptime) return brace;
            if (brace >= 3 and tags[brace - 3] == .keyword_comptime and
                tags[brace - 2] == .identifier and tags[brace - 1] == .colon) return brace;
        }
        return null;
    }

    /// The token naming this function's `comptime <name>: type`
    /// parameter.  The fn prototype is the only place such a binding is
    /// created, and a comptime type parameter is immutable for the
    /// whole body — so a bare identifier naming it denotes one and the
    /// same type wherever it appears.  `*const type` and `anytype` are
    /// rejected: neither is the immutable `type` binding this needs.
    pub fn comptimeTypeParamToken(self: *const Resolver, name: []const u8) ?Ast.TokenIndex {
        const proto = self.fn_proto orelse return null;
        const tree = self.tree;
        var it = proto.iterate(tree);
        while (it.next()) |param| {
            const comptime_tok = param.comptime_noalias orelse continue;
            if (tree.tokenTag(comptime_tok) != .keyword_comptime) continue;
            const name_tok = param.name_token orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(name_tok), name)) continue;
            const type_expr = param.type_expr orelse continue;
            const t_first = tree.firstToken(type_expr);
            const t_last = tree.lastToken(type_expr);
            if (t_first != t_last) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t_first), "type")) continue;
            return name_tok;
        }
        return null;
    }

    /// True when `name` still resolves to the local registered for
    /// `param_tok`.  That registration is the fn parameter's own
    /// declaration position, so a match proves nothing declared inside
    /// the body has shadowed it — no `const T = …`, no `comptime var T
    /// = …`, no capture, no destructured binding.
    pub fn bindingIsParam(self: *const Resolver, name: []const u8, param_tok: Ast.TokenIndex) bool {
        const locals = self.locals orelse return false;
        const lid = locals.by_name.get(name) orelse return false;
        if (@intFromEnum(lid) >= locals.info.items.len) return false;
        const param_byte = self.tree.tokens.items(.start)[param_tok];
        return locals.info.items[@intFromEnum(lid)].decl_pos.byte == param_byte;
    }

    /// Element count of a PARAMETER whose declared type is a fixed
    /// array `[N]E`.  The AST evaluator answers when `N` is written in
    /// this file (`[32]u8`, `[specs.len]u8`); the type engine answers
    /// when it is not, which is the case that matters for a length
    /// belonging to another module:
    ///
    ///     fn hexOfDigest(digest: [Sha256.digest_length]u8) [64]u8
    ///
    /// `Sha256.digest_length` is a real comptime value, and asking
    /// Zig's own analyser for the array length of the declared type
    /// returns it exactly.  Nothing here is inferred from the NAME:
    /// what is resolved is the type, and its length — which is why a
    /// name that resolves to nothing computable, a slice, or an import
    /// the engine cannot read leaves the proof declined rather than
    /// credited on the strength of the spelling.
    ///
    /// The one engine question is the length of the declared array,
    /// which is the element count the analyser reads off the same
    /// `N`.  Asking for `N` again on its own would be the same oracle
    /// query with the same answer, so it is not asked twice.
    fn paramFixedLength(self: *const Resolver, name_tok: Ast.TokenIndex) ?u64 {
        const proto = self.fn_proto orelse return null;
        const tree = self.tree;
        var it = proto.iterate(tree);
        while (it.next()) |param| {
            const param_tok = param.name_token orelse continue;
            if (param_tok != name_tok) continue;
            const type_expr = param.type_expr orelse return null;
            const length = self.arrayLengthOf(.{
                .first = tree.firstToken(type_expr),
                .last = tree.lastToken(type_expr),
            }) orelse return null;
            if (self.comptimeIntTokens(length, 0)) |n| return n;
            const cache = self.cache orelse return null;
            return cache.fixedArrayLenOf(type_expr);
        }
        return null;
    }

    // ── Extents ─────────────────────────────────────────────

    /// Element count of the aggregate a fill writes, from its
    /// DECLARED type token span.  Three shapes fix a count exactly: a
    /// fixed array `[N]E` written out, a fixed array written as
    /// `<collection>.len` — which states its count by naming a
    /// collection, and is the only count a loop needs when the
    /// collection's length is not a constant expression — and a name
    /// bound to `@Tuple(&V)`, whose tuple has exactly `V.len` fields.
    /// Every name is resolved as a visible DECLARATION, so an
    /// unrelated `const` of the same spelling elsewhere in the file is
    /// not what answers here.  Everything else — a slice (`[]E` has no
    /// length), an optional, a sentinel, a named struct, a generic
    /// parameter — is declined.
    pub fn declaredExtent(self: *const Resolver, span: TokenSpan) ?Extent {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (self.arrayLengthOf(span)) |length| {
            if (self.stripLenSuffix(length)) |expr| {
                if (self.enumMetaFieldsTypeSpan(expr)) |type_span| {
                    return .{ .number = self.enumFieldsCount(type_span, 0) orelse return null };
                }
                // `[<collection>.len]E` states its count by naming the
                // collection, and there are exactly two ways that
                // count can be established — each needs its own proof:
                //
                //   - the collection is a field of an AGGREGATE
                //     LITERAL, so its elements are written out and
                //     can simply be counted;
                //   - it is a field of a COMPILER REFLECTION value,
                //     whose shape is a function of the type it
                //     describes, so both sites naming the same
                //     declared value name the same count.
                //
                // Everything else declines, and the interesting case
                // is why: a `const` is not enough.  A `const` pointer
                // to a resizable holder fixes the BINDING, not the
                // length the loop walks, and neither is a field path
                // that leaves the literal a value holds.
                const root_tok = expr.first;
                if (root_tok >= tags.len or tags[root_tok] != .identifier) return null;
                const root = self.visibleConstDecl(root_tok, tree.tokenSlice(root_tok)) orelse return null;
                const path = self.fieldPathOf(expr, root) orelse return null;
                if (self.aggregateFieldCount(path)) |n| return .{ .number = n };
                const id = self.collectionIdOf(path) orelse return null;
                return .{ .collection = id };
            }
            const n = self.comptimeIntTokens(length, 0) orelse return null;
            return .{ .number = n };
        }
        // A bare name: the type is another `const`, and only the two
        // shapes below carry a count we can state exactly.
        if (span.first != span.last) return null;
        if (tags[span.first] != .identifier) return null;
        const decl = self.visibleConstDecl(span.first, tree.tokenSlice(span.first)) orelse return null;
        if (self.tupleVectorOf(decl)) |vector| return .{ .vec = vector };
        // `const Vec = [4]u8;` states its length in the initializer;
        // `const Vec: [4]u8 = …;` states it in the annotation.  Both
        // name the same immutable type, so either answers — but only
        // when the initializer IS that type expression.  A brace in it
        // makes it an array VALUE (`const Vec = [4]u8{ … }` binds a
        // pointer to an array, not the type), whose length says
        // nothing about what `var v: Vec` stores.
        const spans = decl.spans.?;
        const type_span = spans.type orelse spans.init;
        if (!spanHasBrace(tree, type_span)) {
            if (self.arrayLengthOf(type_span)) |length| {
                const n = self.comptimeIntTokens(length, 0) orelse return null;
                return .{ .number = n };
            }
        }
        return null;
    }

    /// Tuple shape supplies a byte-mask extent, not a fill-binding identity.
    pub fn diagnosticTupleExtent(self: *const Resolver, span: TokenSpan) ?u64 {
        const extent = self.declaredExtent(span) orelse return null;
        const vector = extent.vec orelse return null;
        const root = self.visibleConstDecl(span.first, self.tree.tokenSlice(vector)) orelse return null;
        return self.aggregateFieldCount(.{ .root = root, .fields = undefined, .field_count = 0 });
    }

    /// Element count of what a loop enumerates.  A bare identifier —
    /// or a dotted chain rooted in one — must resolve to a `const`
    /// VISIBLE where the loop writes it: the trip count is that
    /// binding's length, so a mutable `var`, a runtime parameter, or a
    /// same-named `const` belonging to some other namespace leaves
    /// nothing to state.  A literal collection needs no binding.
    ///
    /// The count itself comes from the binding's declared type when it
    /// is a fixed array, and otherwise from an array-literal
    /// initializer — which is what a `[]const T` bound to `&.{ … }`
    /// has: the slice type carries no length, but the literal it points
    /// at does.  A field path states its count the same way a target's
    /// `[<it>.len]` does, so both sides of a proof end up asking the
    /// same question of the same declaration.
    pub fn iteratedExtent(self: *const Resolver, input: Ast.Node.Index) ?Extent {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(input);
        const last = tree.lastToken(input);
        if (first > last or last >= tags.len) return null;
        const span = TokenSpan{ .first = first, .last = last };
        const root = self.immutableRootOf(span) orelse {
            const n = arrayLiteralElementCount(tree, span) orelse return null;
            return .{ .number = n };
        };
        const path = self.fieldPathOf(span, root) orelse return null;
        var extent = Extent{
            .collection = self.collectionIdOf(path),
            .number = self.aggregateFieldCount(path),
        };
        // A chain (`info.params`) states a length but is not itself an
        // aggregate a `@Tuple` target could be built over.
        if (span.first != span.last) return extent;
        const spans = root.spans.?;
        extent.vec = root.name_tok;
        if (spans.type) |type_span| {
            if (self.arrayLengthOf(type_span)) |length| {
                extent.number = self.comptimeIntTokens(length, 0);
            }
        }
        if (extent.number == null) {
            extent.number = arrayLiteralElementCount(tree, spans.init);
        }
        return extent;
    }

    /// A runtime enumeration has the target's fixed count when the
    /// immediately preceding statement is the real std.debug.assert
    /// equating their lengths. No intervening statement, conditional
    /// assertion, unrelated binding, or user-defined assert is evidence.
    pub fn assertedEnumerationExtent(
        self: *const Resolver,
        loop: Ast.full.For,
        target_name_tok: Ast.TokenIndex,
        target: Extent,
    ) file_cache.SummaryError!?Extent {
        const count = target.number orelse return null;
        if (loop.ast.inputs.len != 2) return null;
        const tree = self.tree;
        const previous = self.statementBeforeToken(loop.ast.for_token) orelse return null;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, previous) orelse return null;
        if (call.ast.params.len != 1) return null;
        const callee = TokenSpan{
            .first = tree.firstToken(call.ast.fn_expr),
            .last = tree.lastToken(call.ast.fn_expr),
        };
        const tags = tree.tokens.items(.tag);
        if (callee.last != callee.first + 4 or tags[callee.first] != .identifier or
            tags[callee.first + 1] != .period or tags[callee.first + 2] != .identifier or
            tags[callee.first + 3] != .period or tags[callee.last] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(callee.first + 2), "debug") or
            !std.mem.eql(u8, tree.tokenSlice(callee.last), "assert")) return null;
        const namespace = self.visibleConstDecl(callee.first, tree.tokenSlice(callee.first)) orelse return null;
        const initializer = namespace.spans.?.init;
        if (initializer.last != initializer.first + 3 or tags[initializer.first] != .builtin or
            !std.mem.eql(u8, tree.tokenSlice(initializer.first), "@import") or
            tags[initializer.first + 1] != .l_paren or tags[initializer.first + 2] != .string_literal or
            !std.mem.eql(u8, tree.tokenSlice(initializer.first + 2), "\"std\"") or
            tags[initializer.last] != .r_paren) return null;

        const condition = call.ast.params[0];
        if (tree.nodeTag(condition) != .equal_equal) return null;
        const pair = tree.nodeData(condition).node_and_node;
        const input = loop.ast.inputs[0];
        if (!(self.assertedLengthPair(pair[0], pair[1], input, target_name_tok) or
            self.assertedLengthPair(pair[1], pair[0], input, target_name_tok))) return null;
        const cache = self.cache orelse return null;
        const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)) orelse return null;
        if (actual.callee.call_node != previous) return null;
        const declaring_tree = actual.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(declaring_tree, &proto_buffer, actual.callee.declaration) orelse return null;
        const name_token = proto.name_token orelse return null;
        if (!std.mem.eql(u8, declaring_tree.tokenSlice(name_token), "assert")) return null;
        const resolver = if (actual.callee.caller_frame) |frame| frame.resolver else cache.zls orelse return null;
        if (!try resolver.declaredInToolchainFile(actual.callee.handle, "/std/debug.zig")) return null;
        return .{ .number = count };
    }

    fn assertedLengthPair(
        self: *const Resolver,
        input_length: Ast.Node.Index,
        target_length: Ast.Node.Index,
        input: Ast.Node.Index,
        target_name_tok: Ast.TokenIndex,
    ) bool {
        const tree = self.tree;
        const input_span = self.stripLenSuffix(.{
            .first = tree.firstToken(input_length),
            .last = tree.lastToken(input_length),
        }) orelse return false;
        const target_span = self.stripLenSuffix(.{
            .first = tree.firstToken(target_length),
            .last = tree.lastToken(target_length),
        }) orelse return false;
        if (target_span.first != target_span.last or tree.tokenTag(target_span.first) != .identifier) return false;
        const target_binding = self.visibleDeclAt(target_span.first, tree.tokenSlice(target_span.first)) orelse return false;
        if (target_binding.name_tok != target_name_tok) return false;

        const enumeration_span = TokenSpan{ .first = tree.firstToken(input), .last = tree.lastToken(input) };
        if (tree.tokenTag(input_span.first) != .identifier or tree.tokenTag(enumeration_span.first) != .identifier) return false;
        const asserted_root = self.visibleDeclAt(input_span.first, tree.tokenSlice(input_span.first)) orelse return false;
        const iterated_root = self.visibleDeclAt(enumeration_span.first, tree.tokenSlice(enumeration_span.first)) orelse return false;
        if (asserted_root.name_tok != iterated_root.name_tok) return false;
        const asserted_path = self.fieldPathOf(input_span, asserted_root) orelse return false;
        const iterated_path = self.fieldPathOf(enumeration_span, iterated_root) orelse return false;
        if (asserted_path.field_count != iterated_path.field_count) return false;
        for (asserted_path.fields[0..asserted_path.field_count], iterated_path.fields[0..iterated_path.field_count]) |a, b| {
            if (!std.mem.eql(u8, a, b)) return false;
        }
        return true;
    }

    /// Only a direct statement sibling can establish an immediate fact.
    fn statementBeforeToken(self: *const Resolver, token: Ast.TokenIndex) ?Ast.Node.Index {
        const tree = self.tree;
        for (0..tree.nodes.len) |raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            var buffer: [2]Ast.Node.Index = undefined;
            const statements: []const Ast.Node.Index = switch (tree.nodeTag(node)) {
                .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(node).extra_range, Ast.Node.Index),
                .block_two, .block_two_semicolon => blk: {
                    const data = tree.nodeData(node).opt_node_and_opt_node;
                    buffer[0] = data[0].unwrap() orelse continue;
                    buffer[1] = data[1].unwrap() orelse break :blk buffer[0..1];
                    break :blk buffer[0..2];
                },
                else => continue,
            };
            for (statements, 0..) |statement, index_| {
                if (tree.nodeMainToken(statement) != token) continue;
                return if (index_ == 0) null else statements[index_ - 1];
            }
        }
        return null;
    }

    /// How many times a single-input `for (X) |v| …` runs, when the
    /// language pins that count rather than leaving it to a value.
    ///
    /// A `for` over a FIXED-SIZE array always walks all of it — the
    /// trip count is a property of the type, not of the data, so no
    /// zero-trip, partial-trip or reslice hazard exists here the way
    /// it does for a slice.  That is what makes a counter or a
    /// strided write over such a loop countable.  A slice, an
    /// optional, a range, or anything whose length is a runtime
    /// value is declined: `for (someSlice)` walks whatever that
    /// slice currently holds, which is nothing this can state.
    ///
    /// The binding is resolved through [Resolver.visibleDeclAt] rather
    /// than matched by text, so a `const` in another namespace cannot
    /// stand in for this one, and a reference that resolves to a
    /// capture — which names no storage this can count — is refused.
    pub fn iteratedFixedCount(self: *const Resolver, input: Ast.Node.Index) ?u64 {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(input);
        const last = tree.lastToken(input);
        if (first > last or last >= tags.len) return null;
        // A field path is not a collection: `for (tbl.rows)` walks
        // rows, whose length is not what any binding here fixes.
        if (first != last) return null;
        if (tags[first] != .identifier) return null;
        const decl = self.visibleDeclAt(first, tree.tokenSlice(first)) orelse return null;
        if (decl.spans) |spans| {
            if (spans.type) |type_span| {
                const length = self.arrayLengthOf(type_span) orelse return null;
                return self.comptimeIntTokens(length, 0);
            }
            return arrayLiteralElementCount(tree, spans.init);
        }
        // A PARAMETER.  Its declared type fixes its length for every
        // call, so `[32]u8` counts as thirty-two without the caller
        // being consulted.  The declaration token has to be the
        // prototype's own, or this would be answering for a capture
        // that merely shares the name.
        return self.paramFixedLength(decl.name_tok);
    }

    /// The immutable declaration a `const X = @Tuple(&V);` initializer
    /// measures.  `@Tuple` builds one field per element of its
    /// argument, so the tuple's field count IS `V.len` — which is only
    /// the same count the loop writes when `V` is the same declaration
    /// at both sites.
    fn tupleVectorOf(self: *const Resolver, decl: ScopedDecl) ?Ast.TokenIndex {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const vector_span = decl.spans.?.init;
        if (vector_span.first > vector_span.last or vector_span.last >= tags.len) return null;
        if (vector_span.last != vector_span.first + 4) return null;
        if (tags[vector_span.first] != .builtin) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(vector_span.first), "@Tuple")) return null;
        if (tags[vector_span.first + 1] != .l_paren) return null;
        if (tags[vector_span.first + 2] != .ampersand) return null;
        if (tags[vector_span.first + 3] != .identifier) return null;
        if (tags[vector_span.first + 4] != .r_paren) return null;
        const vector_tok = vector_span.first + 3;
        const root = self.visibleConstDecl(vector_tok, tree.tokenSlice(vector_tok)) orelse return null;
        return root.name_tok;
    }

    /// The `<expr>` of a length written `<expr>.len`.  Null for a bare
    /// literal, a sum, a call — every shape whose count this does not
    /// state.
    fn stripLenSuffix(self: *const Resolver, span: TokenSpan) ?TokenSpan {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const last = span.last;
        if (last < span.first + 2 or last >= tags.len) return null;
        if (tags[last] != .identifier) return null;
        if (tags[last - 1] != .period) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(last), "len")) return null;
        return .{ .first = span.first, .last = last - 2 };
    }

    /// The immutable `const` a length expression reads its length
    /// from.  `span` must be a bare identifier or a dotted chain
    /// rooted in one (`func_info.params`); only the ROOT is resolved,
    /// because that is the binding whose fixed value — and so whose
    /// `.len` — both sides read.
    ///
    /// A `var` root is refused on purpose: it can be reassigned or
    /// resliced between the target's declaration and the loop, and
    /// then the count the target was given is not the count the loop
    /// walks.
    fn immutableRootOf(self: *const Resolver, span: TokenSpan) ?ScopedDecl {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (tags[span.first] != .identifier) return null;
        var t: Ast.TokenIndex = span.first + 1;
        while (t <= span.last) {
            if (tags[t] != .period) return null;
            if (t + 1 > span.last or tags[t + 1] != .identifier) return null;
            t += 2;
        }
        return self.visibleConstDecl(span.first, tree.tokenSlice(span.first));
    }

    /// Split a length expression into the binding it is rooted in and
    /// the field path walked from it.  `root` is that binding's
    /// already-resolved declaration, so this costs no second file
    /// scan — the caller has it in hand.
    ///
    /// A subscript, a deref, a call and an optional unwrap are all
    /// refused: each of those steps through STORAGE rather than
    /// through a struct's own fields, and a count read through storage
    /// is not one this can pin.
    fn fieldPathOf(self: *const Resolver, span: TokenSpan, root: ScopedDecl) ?FieldPath {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (tags[span.first] != .identifier) return null;
        var path = FieldPath{
            .root = root,
            .fields = undefined,
            .field_count = 0,
        };
        var t: Ast.TokenIndex = span.first + 1;
        while (t <= span.last) : (t += 2) {
            if (tags[t] != .period) return null;
            if (t + 1 > span.last or tags[t + 1] != .identifier) return null;
            if (path.field_count == max_fill_path_fields) return null;
            path.fields[path.field_count] = tree.tokenSlice(t + 1);
            path.field_count += 1;
        }
        return path;
    }

    /// The element count a field path states, read straight off the
    /// AGGREGATE LITERAL the binding is initialized with.
    ///
    /// Each step must be a field that literal actually DESIGNATES,
    /// and the value it designates must itself be a brace literal —
    /// either to walk one more step, or, at the end, to count.  A
    /// literal is written out in the source, so the field holds
    /// exactly what is shown and no statement can resize it.  Nothing
    /// is inferred from any type, and in particular no step is assumed
    /// to be a field rather than a pointer: every step is checked.
    ///
    /// A path that LEAVES the literal is declined, because what it
    /// reaches is storage this cannot see:
    ///
    ///     const outer = Outer{ .child = &holder };
    ///     outer.child.items.len
    ///
    /// `outer` is a value and `outer.child` is a `*Holder`, so the
    /// `.len` read at the end is `holder`'s and not the literal's — and
    /// `holder` can still be resized.  A root being a value is
    /// therefore no evidence at all; the whole path, ending in
    /// something countable, is.
    fn aggregateFieldCount(self: *const Resolver, path: FieldPath) ?u64 {
        const spans = path.root.spans orelse return null;
        var value = spans.init;
        var i: u8 = 0;
        while (i < path.field_count) : (i += 1) {
            value = designatedFieldInit(self.tree, value, path.fields[i]) orelse return null;
        }
        return arrayLiteralElementCount(self.tree, value);
    }

    /// The reflection collection a field path reads, or null when the
    /// path is not over a compiler reflection value.
    fn collectionIdOf(self: *const Resolver, path: FieldPath) ?CollectionId {
        if (!self.bindingHoldsReflectionValue(path.root)) return null;
        return .{
            .root = path.root.name_tok,
            .fields = path.fields,
            .field_count = path.field_count,
        };
    }

    /// Does this `const` bind a COMPILER REFLECTION value — what
    /// `@typeInfo(<type>)` returns, optionally narrowed by field
    /// accesses?
    ///
    /// `@typeInfo` is a comptime builtin: it takes a type and returns
    /// that type's description, so the whole tree it yields — every
    /// field, and every element of a field that is itself a
    /// description — is a function of the type argument and of
    /// nothing else.  No statement can write to it, and the type
    /// argument is fixed for the function, so a `.len` read anywhere
    /// under it is the same number at every read.  That is what lets a
    /// generated wrapper size its own target with
    /// `[func_info.params.len]type` and then walk
    /// `func_info.params`.
    ///
    /// This is a statement about what the LANGUAGE computes, not about
    /// any name, and it is the ONLY builtin whose result is treated
    /// this way.  Every other initializer is declined, because
    /// nothing here can show what it produces.  A function call and a
    /// bare name are obvious; the ones that need saying are `@as` and
    /// `@bitCast`, whose result TYPE the call chooses and may choose
    /// to be a pointer; `@call`, whose result is whatever the callee
    /// returns; `@field`, which hands back the named field, a pointer
    /// field included; `@unionInit`, whose result can carry one;
    /// `@extern` and `@embedFile`, which are addresses outright; and
    /// `@errorReturnTrace`, `@cVaStart` and `@cVaArg`, which carry
    /// pointers and optionals.  Treating an UNLISTED builtin as a
    /// value would be a guess, and a guess in this direction is
    /// precisely how a resizable `.len` comes to be treated as fixed.
    fn bindingHoldsReflectionValue(self: *const Resolver, decl: ScopedDecl) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const spans = decl.spans orelse return false;
        // The rule is about the value `@typeInfo` computes; an
        // annotation would be a claim about a type instead.
        if (spans.type != null) return false;
        const descriptor = spans.init;
        if (descriptor.first > descriptor.last or descriptor.last >= tags.len) return false;
        if (tags[descriptor.first] != .builtin) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(descriptor.first), "@typeInfo")) return false;
        if (descriptor.first + 1 >= tags.len or tags[descriptor.first + 1] != .l_paren) return false;
        const close = tokens.matchParen(tags, descriptor.first + 1, descriptor.last) orelse return false;
        // Everything past the call must be field selection: the
        // descriptor itself, and any narrowing of it.
        var t: Ast.TokenIndex = close + 1;
        while (t <= descriptor.last) : (t += 1) {
            if (tags[t] != .period) return false;
            t += 1;
            if (t > descriptor.last or tags[t] != .identifier) return false;
        }
        return true;
    }

    // ── Comptime integer expressions ───────────────────────

    /// Length-expression token span of a fixed array type written
    /// `[N]E`.  Null for a slice (`[]E`, an empty span), for a
    /// sentinel (`[N:s]E`), for a nested bracket, and for a span with
    /// no element type after the closing bracket.
    /// Balanced parentheses are extracted, not evaluated; the count resolver
    /// still accepts only its authenticated constant-expression grammar.
    pub fn arrayLengthOf(self: *const Resolver, span: TokenSpan) ?TokenSpan {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (tags[span.first] != .l_bracket) return null;
        var t: Ast.TokenIndex = span.first + 1;
        var parentheses: u32 = 0;
        while (t <= span.last and t < tags.len) : (t += 1) {
            switch (tags[t]) {
                .l_bracket, .l_brace, .colon => return null,
                .l_paren => parentheses += 1,
                .r_paren => {
                    if (parentheses == 0) return null;
                    parentheses -= 1;
                },
                .r_bracket => {
                    if (parentheses != 0) return null;
                    if (t == span.first + 1) return null;
                    if (t == span.last) return null;
                    return .{ .first = span.first + 1, .last = t - 1 };
                },
                else => {},
            }
        }
        return null;
    }

    /// Integer value of a span that is exactly one integer literal.
    pub fn literalValue(self: *const Resolver, span: TokenSpan) ?u64 {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (span.first != span.last) return null;
        if (tags[span.first] != .number_literal) return null;
        return std.fmt.parseInt(u64, tree.tokenSlice(span.first), 0) catch null;
    }

    /// Integer value of a comptime length expression, from a closed
    /// grammar: decimal literals, `+` / `-` between them, parentheses,
    /// and references to a `const` in this file whose initializer is
    /// itself such an expression.  Nothing else — no call, no field
    /// access, no `@sizeOf`, no enum field — is guessed at, so the
    /// answer is exact or absent.
    pub fn comptimeIntTokens(self: *const Resolver, span: TokenSpan, depth: u32) ?u64 {
        if (depth > max_fill_eval_depth) return null;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (span.last - span.first + 1 > max_fill_eval_tokens) return null;
        var eval = FillIntEval{
            .resolver = self,
            .tree = tree,
            .tags = tags,
            .pos = span.first,
            .end = span.last,
            .depth = depth,
        };
        const value = eval.expr() orelse return null;
        // Trailing tokens mean this was not the expression it looked
        // like (`a + b * c`, `f(x)`); an unanswered question, not a
        // number.
        if (eval.pos <= eval.end) return null;
        return value;
    }

    /// Resolve only genuine `std.meta.fields(Type)`, not a lookalike call.
    pub fn enumMetaFieldsTypeSpan(self: *const Resolver, span: TokenSpan) ?TokenSpan {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        const first = span.first;
        if (span.last - first < 7 or tags[first] != .identifier or
            tags[first + 1] != .period or tags[first + 2] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(first + 2), "meta") or
            tags[first + 3] != .period or tags[first + 4] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(first + 4), "fields") or
            tags[first + 5] != .l_paren or tags[span.last] != .r_paren) return null;
        const root = self.visibleConstDecl(first, tree.tokenSlice(first)) orelse return null;
        const initializer = root.spans.?.init;
        if (initializer.last - initializer.first != 3 or tags[initializer.first] != .builtin or
            !std.mem.eql(u8, tree.tokenSlice(initializer.first), "@import") or
            tags[initializer.first + 1] != .l_paren or tags[initializer.first + 2] != .string_literal or
            !std.mem.eql(u8, tree.tokenSlice(initializer.first + 2), "\"std\"") or
            tags[initializer.last] != .r_paren) return null;
        const arg = TokenSpan{ .first = first + 6, .last = span.last - 1 };
        var token = arg.first;
        while (token <= arg.last) {
            if (tags[token] != .identifier) return null;
            if (token == arg.last) break;
            if (token + 2 > arg.last or tags[token + 1] != .period) return null;
            token += 2;
        }
        return arg;
    }

    /// Reflection length remains the declared field count, not the tag maximum.
    pub fn enumFieldsCount(self: *const Resolver, type_span: TokenSpan, depth: u32) ?u64 {
        if (type_span.first == type_span.last)
            return self.enumFieldCount(type_span.first, depth);
        const declaration = self.enumContainerOf(type_span, depth) orelse return null;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = declaration.tree.fullContainerDecl(&buffer, declaration.node) orelse return null;
        var count: u64 = 0;
        for (container.ast.members) |member| {
            if (declaration.tree.fullContainerField(member) == null) continue;
            if (std.mem.eql(u8, declaration.tree.tokenSlice(
                declaration.tree.nodeMainToken(member),
            ), "_")) continue;
            count += 1;
        }
        return count;
    }

    const EnumContainer = struct {
        tree: *const Ast,
        node: Ast.Node.Index,
    };

    /// Chase the same lexical aliases and canonical imports used by enum counts.
    fn enumContainerOf(self: *const Resolver, type_span: TokenSpan, depth: u32) ?EnumContainer {
        if (depth > max_fill_eval_depth) return null;
        const tree = self.tree;
        if (type_span.first > type_span.last or type_span.last >= tree.tokens.len or
            tree.tokenTag(type_span.first) != .identifier) return null;
        if (type_span.first == type_span.last) {
            const decl = self.visibleConstDecl(
                type_span.first,
                tree.tokenSlice(type_span.first),
            ) orelse return null;
            const initializer = decl.spans.?.init;
            if (tree.tokenTag(initializer.first) != .keyword_enum)
                return self.enumContainerOf(initializer, depth + 1);
            for (0..tree.nodes.len) |raw| {
                const node: Ast.Node.Index = @enumFromInt(raw);
                if (tree.lastToken(node) == initializer.last and
                    tree.tokenTag(tree.nodeMainToken(node)) == .keyword_enum)
                    return .{ .tree = tree, .node = node };
            }
            return null;
        }
        const root = self.visibleConstDecl(
            type_span.first,
            tree.tokenSlice(type_span.first),
        ) orelse return null;
        if (root.scope_len != 0) return null;
        var segments: [max_fill_path_fields][]const u8 = undefined;
        var count: usize = 0;
        var token = type_span.first;
        while (token <= type_span.last) {
            if (count == segments.len or tree.tokenTag(token) != .identifier) return null;
            segments[count] = tree.tokenSlice(token);
            count += 1;
            if (token == type_span.last) break;
            if (token + 2 > type_span.last or tree.tokenTag(token + 1) != .period) return null;
            token += 2;
        }
        const cache = self.cache orelse return null;
        const resolved = cache.importedTypeAcrossImports(segments[0..count]) orelse return null;
        if (resolved.info.kind != .enum_) return null;
        const enum_tree = resolved.model.tree;
        for (0..enum_tree.nodes.len) |raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (enum_tree.lastToken(node) == resolved.info.body_last and
                enum_tree.tokenTag(enum_tree.nodeMainToken(node)) == .keyword_enum)
                return .{ .tree = enum_tree, .node = node };
        }
        return null;
    }

    /// Prove each tag's actual value equals its zero-based declaration ordinal.
    /// This ordered bijection proves complete coverage without a guessed extent.
    pub fn contiguousEnumValueCount(self: *const Resolver, type_span: TokenSpan) ?u64 {
        const declaration = self.enumContainerOf(type_span, 0) orelse return null;
        const tree = declaration.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, declaration.node) orelse return null;
        var foreign = Resolver.init(self.gpa, tree, null, null);
        defer foreign.deinit();
        const evaluator = if (tree == self.tree) self else &foreign;
        var count: u64 = 0;
        for (container.ast.members) |member| {
            const field = tree.fullContainerField(member) orelse continue;
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(member)), "_")) return null;
            if (field.ast.value_expr.unwrap()) |value| {
                const actual = evaluator.comptimeIntTokens(.{
                    .first = tree.firstToken(value),
                    .last = tree.lastToken(value),
                }, 0) orelse return null;
                if (actual != count) return null;
            }
            // With every preceding explicit tag equal to its ordinal, implicit
            // tags have exactly this next value; no hole or duplicate is possible.
            count += 1;
        }
        return count;
    }

    /// Actual reflected tags describe possible destinations, not coverage.
    pub fn enumValueIndices(self: *const Resolver, type_span: TokenSpan) !?[]u64 {
        const declaration = self.enumContainerOf(type_span, 0) orelse return null;
        const tree = declaration.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, declaration.node) orelse return null;
        var foreign = Resolver.init(self.gpa, tree, null, null);
        defer foreign.deinit();
        const evaluator = if (tree == self.tree) self else &foreign;
        var values: std.ArrayListUnmanaged(u64) = .empty;
        defer values.deinit(self.gpa);
        var next: u64 = 0;
        for (container.ast.members) |member| {
            const field = tree.fullContainerField(member) orelse continue;
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(member)), "_")) return null;
            const actual = if (field.ast.value_expr.unwrap()) |value|
                evaluator.comptimeIntTokens(.{ .first = tree.firstToken(value), .last = tree.lastToken(value) }, 0) orelse return null
            else
                next;
            try values.append(self.gpa, actual);
            next = std.math.add(u64, actual, 1) catch return null;
        }
        return try values.toOwnedSlice(self.gpa);
    }

    /// Value of the `const` a reference at `name_tok` resolves to,
    /// chased one binding at a time.
    fn constIntBinding(self: *const Resolver, name_tok: Ast.TokenIndex, depth: u32) ?u64 {
        if (depth > max_fill_eval_depth) return null;
        const tree = self.tree;
        const decl = self.visibleConstDecl(name_tok, tree.tokenSlice(name_tok)) orelse return null;
        return self.comptimeIntTokens(decl.spans.?.init, depth);
    }

    /// Count declared enum fields, not tag values or an unrelated literal.
    fn enumFieldCount(self: *const Resolver, name_tok: Ast.TokenIndex, depth: u32) ?u64 {
        if (depth > max_fill_eval_depth) return null;
        const tree = self.tree;
        const decl = self.visibleConstDecl(name_tok, tree.tokenSlice(name_tok)) orelse return null;
        const initializer = decl.spans.?.init;
        if (initializer.first == initializer.last and tree.tokenTag(initializer.first) == .identifier)
            return self.enumFieldCount(initializer.first, depth + 1);
        var enum_tree = tree;
        var enum_last = initializer.last;
        if (tree.tokenTag(initializer.first) != .keyword_enum) {
            // Resolve the exact qualified import path to its declaration.
            // A local shadow of the root must never use a file-root import.
            if (decl.scope_len != 0 or tree.tokenTag(initializer.first) != .identifier) return null;
            const root = self.visibleConstDecl(initializer.first, tree.tokenSlice(initializer.first)) orelse return null;
            if (root.scope_len != 0) return null;
            var segments: [max_fill_path_fields][]const u8 = undefined;
            var count: usize = 0;
            var token = initializer.first;
            while (token <= initializer.last) {
                if (count == segments.len or tree.tokenTag(token) != .identifier) return null;
                segments[count] = tree.tokenSlice(token);
                count += 1;
                if (token == initializer.last) break;
                if (token + 2 > initializer.last or tree.tokenTag(token + 1) != .period) return null;
                token += 2;
            }
            const cache = self.cache orelse return null;
            const resolved = cache.importedTypeAcrossImports(segments[0..count]) orelse return null;
            if (resolved.info.kind != .enum_) return null;
            enum_tree = resolved.model.tree;
            enum_last = resolved.info.body_last;
        }
        for (0..enum_tree.nodes.len) |raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (enum_tree.lastToken(node) != enum_last or
                enum_tree.tokenTag(enum_tree.nodeMainToken(node)) != .keyword_enum) continue;
            var buffer: [2]Ast.Node.Index = undefined;
            const container = enum_tree.fullContainerDecl(&buffer, node) orelse continue;
            var count: u64 = 0;
            for (container.ast.members) |member| {
                if (enum_tree.fullContainerField(member) == null) continue;
                if (std.mem.eql(u8, enum_tree.tokenSlice(enum_tree.nodeMainToken(member)), "_")) continue;
                count += 1;
            }
            return count;
        }
        return null;
    }

    /// Element count of the `const` a `<name>.len` reference reads,
    /// chased one binding at a time.
    ///
    /// The `.len` is only as good as the storage behind the binding,
    /// so exactly two shapes answer and the rest decline:
    ///
    ///   - a `const` ANNOTATED with a fixed array type.  The
    ///     annotation fixes the length, the binding cannot be
    ///     rebound, and nothing the program can do resizes a
    ///     `var`-less array value.
    ///   - a `const` bound DIRECTLY to an array literal written out in
    ///     this file.  Its storage is counted, and a `const` binding
    ///     cannot be repointed.
    ///
    /// What deliberately does NOT answer is a path through a field,
    /// and that is the interesting case:
    ///
    ///     const holder = Holder{ .items = &.{ 1, 2, 3 } };
    ///     const count = holder.items.len;
    ///
    /// `holder` is a `const` VALUE, and `holder.items` is a slice
    /// field.  Whoever holds `&holder` can reassign or reslice that
    /// field, so the length read here is not one this analysis can
    /// pin — the same reason `designatedFieldInit` refuses a path
    /// that leaves a literal.  Reading `<name>.len` with no field
    /// path is the case that survives.
    fn constLenBinding(self: *const Resolver, name_tok: Ast.TokenIndex, depth: u32) ?u64 {
        if (depth > max_fill_eval_depth) return null;
        const tree = self.tree;
        const decl = self.visibleConstDecl(name_tok, tree.tokenSlice(name_tok)) orelse return null;
        const spans = decl.spans.?;
        if (spans.type) |type_span| {
            const length = self.arrayLengthOf(type_span) orelse return null;
            return self.comptimeIntTokens(length, depth);
        }
        return arrayLiteralElementCount(tree, spans.init);
    }
};

const FillIntEval = struct {
    resolver: *const Resolver,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    pos: Ast.TokenIndex,
    end: Ast.TokenIndex,
    depth: u32,

    fn expr(self: *FillIntEval) ?u64 {
        var acc = self.term() orelse return null;
        while (self.pos <= self.end) {
            const tag = self.tags[self.pos];
            if (tag != .plus and tag != .minus) break;
            self.pos += 1;
            const rhs = self.term() orelse return null;
            if (tag == .minus) {
                // A comptime-negative length can't be written, so
                // this is not a value a real type has.
                if (rhs > acc) return null;
                acc -= rhs;
            } else {
                acc = std.math.add(u64, acc, rhs) catch return null;
            }
        }
        return acc;
    }

    /// `*` binds tighter than the additive loop in `expr`, so
    /// `a * b + c` is `(a * b) + c`.  A product is what a count
    /// built from two nested enumerations states, so evaluating
    /// one here is not a convenience — it is the only way such a
    /// length can be read at all.
    fn term(self: *FillIntEval) ?u64 {
        var acc = self.factor() orelse return null;
        while (self.pos <= self.end and self.tags[self.pos] == .asterisk) {
            self.pos += 1;
            const rhs = self.factor() orelse return null;
            acc = std.math.mul(u64, acc, rhs) catch return null;
        }
        return acc;
    }

    fn factor(self: *FillIntEval) ?u64 {
        if (self.pos > self.end) return null;
        switch (self.tags[self.pos]) {
            .number_literal => {
                const text = self.tree.tokenSlice(self.pos);
                const value = std.fmt.parseInt(u64, text, 0) catch return null;
                self.pos += 1;
                return value;
            },
            .builtin => {
                const first = self.pos;
                // Exact @typeInfo(Name).@"enum".fields.len syntax.
                if (first + 9 > self.end or
                    !std.mem.eql(u8, self.tree.tokenSlice(first), "@typeInfo") or
                    self.tags[first + 1] != .l_paren or self.tags[first + 2] != .identifier or
                    self.tags[first + 3] != .r_paren or self.tags[first + 4] != .period or
                    self.tags[first + 5] != .identifier or
                    !std.mem.eql(u8, self.tree.tokenSlice(first + 5), "@\"enum\"") or
                    self.tags[first + 6] != .period or
                    !std.mem.eql(u8, self.tree.tokenSlice(first + 7), "fields") or
                    self.tags[first + 8] != .period or
                    !std.mem.eql(u8, self.tree.tokenSlice(first + 9), "len")) return null;
                self.pos += 10;
                return self.resolver.enumFieldCount(first + 2, self.depth + 1);
            },
            .identifier => {
                const name_tok = self.pos;
                // A genuine std.meta.fields(Type).len counts the declaration
                // selected by Type, including qualified imported enum types.
                var close = name_tok;
                while (close <= self.end and self.tags[close] != .r_paren) : (close += 1) {}
                if (close + 2 <= self.end and self.tags[close + 1] == .period and
                    std.mem.eql(u8, self.tree.tokenSlice(close + 2), "len"))
                {
                    if (self.resolver.enumMetaFieldsTypeSpan(.{ .first = name_tok, .last = close })) |type_span| {
                        self.pos = close + 3;
                        return self.resolver.enumFieldsCount(type_span, self.depth + 1);
                    }
                }
                self.pos += 1;
                // `<collection>.len` is a count written the way
                // the language spells counts, and reading it is
                // exactly as decidable as the collection it names
                // — see `constLenBinding` for the shapes that
                // answer and, more importantly, the one that does
                // not.
                if (self.pos + 1 <= self.end and
                    self.tags[self.pos] == .period and
                    self.tags[self.pos + 1] == .identifier and
                    std.mem.eql(u8, self.tree.tokenSlice(self.pos + 1), "len"))
                {
                    self.pos += 2;
                    return self.resolver.constLenBinding(name_tok, self.depth + 1);
                }
                return self.resolver.constIntBinding(name_tok, self.depth + 1);
            },
            .l_paren => {
                self.pos += 1;
                const value = self.expr() orelse return null;
                if (self.pos > self.end) return null;
                if (self.tags[self.pos] != .r_paren) return null;
                self.pos += 1;
                return value;
            },
            else => return null,
        }
    }
};

// ── Brace-literal elements ────────────────────────────────

/// ONE walk over the interior of a brace literal.
///
/// Counting how many elements `.{ a, b, c }` has and finding the
/// `.name = <init>` element of `.{ .x = 1, .y = 2 }` are the same
/// question — "where does the next TOP-LEVEL element begin and end" —
/// and they are answered here once.  Two hand-rolled depth loops over
/// the same `{ … }` body were two places for the definition of
/// "top-level" to drift apart; this iterator is the definition, and
/// both callers are projections of it.
///
/// A top-level comma ends the element in progress.  A brace, paren or
/// bracket raises the depth so a comma inside one element cannot split
/// it, and — the clause that is easy to lose — a nested comma must not
/// clear the element in progress either, or `.{ .{ 1, 2 }, .{}, .{ 3 } }`
/// loses the element whose own comma came first and counts two.  A
/// string literal is one token and cannot split an element at all.
pub const ElementIterator = struct {
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    /// Token of this literal's closing `}`.
    close: Ast.TokenIndex,
    /// First token of the element the next [ElementIterator.next] will
    /// return.
    element_first: Ast.TokenIndex,
    finished: bool = false,

    /// The iterator over `span`'s elements, or null when `span` is not
    /// a brace literal at all.
    ///
    /// An `&` in front of the literal is ACCEPTED here: `&.{ 1, 2 }`
    /// really is a literal with two elements.  A caller that must not
    /// follow the pointer — one reading a field out of it — refuses
    /// the `&` itself, because that is a statement about the VALUE,
    /// not about where its elements end.
    pub fn init(tree: *const Ast, span: TokenSpan) ?ElementIterator {
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        const open = braceLiteralOpen(tree, span) orelse return null;
        // `braceLiteralOpen` has already established that the token at
        // `span.last` is this literal's closing delimiter, and it only
        // ever returns a `{`, so the shared matcher answers — this
        // module has no second copy of the same depth count to keep in
        // step.
        const close = tokens.matchBrace(tags, open, span.last) orelse return null;
        return .{ .tree = tree, .tags = tags, .close = close, .element_first = open + 1 };
    }

    /// The next top-level element's token span, delimiters excluded,
    /// or null once the literal is exhausted.
    ///
    /// An EMPTY run between two separators is not an element: nothing
    /// was written there to count or to designate, so `.{ 1, , 2 }`
    /// has two elements and not three.
    ///
    /// Unbalanced delimiters STOP the walk with nothing, rather than
    /// guessing: a closer reaching depth zero anywhere but the
    /// literal's own `}` means the spans this iterator hands back
    /// cannot be trusted to name the element they came from.  The
    /// literal's own balance is already established by
    /// [ElementIterator.init], so this is the direction that can only
    /// lose a proof.
    pub fn next(self: *ElementIterator) ?TokenSpan {
        if (self.finished) return null;
        while (true) {
            var depth: u32 = 0;
            var t: Ast.TokenIndex = self.element_first;
            while (t <= self.close) : (t += 1) {
                switch (self.tags[t]) {
                    .l_brace, .l_paren, .l_bracket => depth += 1,
                    .r_brace, .r_paren, .r_bracket => {
                        if (depth != 0) {
                            depth -= 1;
                            continue;
                        }
                        if (self.tags[t] != .r_brace or t != self.close) {
                            self.finished = true;
                            return null;
                        }
                        self.finished = true;
                        return finish(self.element_first, self.close);
                    },
                    .comma => {
                        if (depth != 0) continue;
                        const first = self.element_first;
                        self.element_first = t + 1;
                        if (first >= t) continue;
                        return .{ .first = first, .last = t - 1 };
                    },
                    else => {},
                }
            }
            self.finished = true;
            return null;
        }
    }

    /// The last element of the literal, when it is not empty.
    fn finish(first: Ast.TokenIndex, close: Ast.TokenIndex) ?TokenSpan {
        if (first >= close) return null;
        return .{ .first = first, .last = close - 1 };
    }
};

/// Element count of an array-literal token span — `.{ … }`,
/// `{ … }`, `[_]T{ … }` / `[N]T{ … }`, or any of those behind a `&`.
/// Counts the pieces between TOP-LEVEL commas, so `.{ }` is 0 and
/// `.{ x }` (no comma) is 1.  Nested braces, parens and brackets raise
/// the depth so a comma inside one element does not split it; a string
/// literal is a single token and cannot split either.  Null when the
/// span is not a brace literal at all — a bare type (`[N]T` has no
/// elements to count), a call, a field access, a named binding.
fn arrayLiteralElementCount(tree: *const Ast, span: TokenSpan) ?u64 {
    var elements = ElementIterator.init(tree, span) orelse return null;
    var count: u64 = 0;
    while (elements.next()) |_| count += 1;
    return count;
}

/// The initializer a DESIGNATED field of a brace literal carries —
/// the `.name = <init>` element of `{ … }`, `.{ … }` or `[N]T{ … }`.
/// The span returned is the whole element after the `=`, so it is the
/// designated value's own source and can be walked into.  Null when
/// `span` is not a brace literal, designates no such field, or
/// designates an empty one.
///
/// Only DESIGNATED fields are matched.  A positional element of a
/// tuple literal has no name, so a path through one stops here rather
/// than guessing which element a field name meant.
fn designatedFieldInit(tree: *const Ast, span: TokenSpan, name: []const u8) ?TokenSpan {
    // A pointer to an aggregate is not the aggregate's immutable value.
    // Following it could observe fields changed through another
    // handle.  This is about the VALUE, not about the elements, so it
    // is refused here rather than by the iterator every count shares.
    if (span.first > span.last or span.last >= tree.tokens.len) return null;
    if (tree.tokenTag(span.first) == .ampersand) return null;
    var elements = ElementIterator.init(tree, span) orelse return null;
    while (elements.next()) |element| {
        if (designatedValueSpan(tree, element.first, element.last, name)) |value| return value;
    }
    return null;
}

/// The value part of one brace-literal element, when that element is
/// the designated field `.name = <value>` (or `.name: <value>`).
fn designatedValueSpan(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    name: []const u8,
) ?TokenSpan {
    const tags = tree.tokens.items(.tag);
    if (first + 3 > last or last >= tags.len) return null;
    if (tags[first] != .period) return null;
    if (tags[first + 1] != .identifier) return null;
    if (tags[first + 2] != .equal and tags[first + 2] != .colon) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(first + 1), name)) return null;
    return .{ .first = first + 3, .last = last };
}

// ── Token parsers ─────────────────────────────────────────

/// Opening brace of a complete aggregate literal, optionally addressed.
/// Named struct literals and fixed-array literals share this parser.
/// Calls, suffix operations, and unresolved element-type bodies decline.
fn braceLiteralOpen(tree: *const Ast, span: TokenSpan) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (span.first > span.last or span.last >= tags.len) return null;
    var open: Ast.TokenIndex = span.first;
    if (tags[open] == .ampersand) {
        open += 1;
        if (open > span.last) return null;
    }
    if (tags[open] == .l_bracket) {
        // `[_]T{ … }` / `[N]T{ … }` — skip the element-type prefix up
        // to the literal's brace.
        var depth: u32 = 0;
        while (true) {
            if (open > span.last) return null;
            switch (tags[open]) {
                .l_bracket => depth += 1,
                .r_bracket => {
                    if (depth == 0) return null;
                    depth -= 1;
                },
                .l_brace => {
                    if (depth != 0) return null;
                    return if (tokens.matchBrace(tags, open, span.last) == span.last) open else null;
                },
                .keyword_struct, .keyword_union, .keyword_enum => {
                    // An inline element type: skip its balanced body (and any
                    // `(tag)` header) to reach the literal's own brace.
                    var body = open + 1;
                    if (body <= span.last and tags[body] == .l_paren) {
                        body = (tokens.matchParen(tags, body, span.last) orelse return null) + 1;
                    }
                    if (body > span.last or tags[body] != .l_brace) return null;
                    open = tokens.matchBrace(tags, body, span.last) orelse return null;
                },
                else => {},
            }
            open += 1;
        }
    } else if (tags[open] == .period) {
        open += 1;
        if (open > span.last or tags[open] != .l_brace) return null;
    } else if (tags[open] == .identifier) {
        open += 1;
        while (open < span.last and tags[open] == .period) {
            if (tags[open + 1] != .identifier) return null;
            open += 2;
        }
        if (open > span.last or tags[open] != .l_brace) return null;
    } else if (tags[open] != .l_brace) return null;
    return if (tokens.matchBrace(tags, open, span.last) == span.last) open else null;
}

/// The `{` tokens still open at `limit`, outermost first.  Every
/// block, container body and braced value opens one, so this chain is
/// what says which regions a reference sits inside.  Null when the
/// nesting runs deeper than the caller's fixed buffer, which the
/// caller answers by declining.
fn openBraceStack(
    tags: []const std.zig.Token.Tag,
    limit: Ast.TokenIndex,
    out: []Ast.TokenIndex,
) ?usize {
    var count: usize = 0;
    var t: Ast.TokenIndex = 0;
    while (t < limit and t < tags.len) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (count == out.len) return null;
                out[count] = t;
                count += 1;
            },
            .r_brace => {
                if (count > 0) count -= 1;
            },
            else => {},
        }
    }
    return count;
}

/// The declaration a `const <name>` token introduces: its optional
/// type annotation and its initializer span.  Null unless the tokens
/// after the name really are `= <expr>;` (or `: <type> = <expr>;`) —
/// a `|const x|` capture and a `for`/`switch` payload are declined
/// here rather than being read as a scalar binding.
pub fn parseConstDeclAt(tree: *const Ast, name_tok: Ast.TokenIndex) ?FileConstDecl {
    const tags = tree.tokens.items(.tag);
    if (name_tok == 0 or name_tok + 1 >= tags.len) return null;
    if (tags[name_tok] != .identifier) return null;
    if (tags[name_tok - 1] != .keyword_const) return null;
    // `const a, const b, const c = .{ … };` DESTRUCTURES: `b` and `c`
    // name ELEMENTS of the initializer tuple, not the tuple.  Reading
    // `c` as the whole `.{ … }` credits it with the length of the thing
    // it destructures — three descriptors for a one-element payload —
    // and a fill measured by that count leaves its tail unwritten.  A
    // scalar `const b = …` is always preceded by `const` alone; the
    // `, const` in front of the name is what makes this a later arm of
    // a destructuring.
    if (name_tok >= 2 and tags[name_tok - 2] == .comma) return null;

    var u: Ast.TokenIndex = name_tok + 1;
    var type_span: ?TokenSpan = null;
    if (u < tags.len and tags[u] == .colon) {
        const type_first = u + 1;
        var depth: u32 = 0;
        var t: Ast.TokenIndex = type_first;
        while (t < tags.len) : (t += 1) {
            switch (tags[t]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => {
                    if (depth == 0) return null;
                    depth -= 1;
                },
                .equal, .semicolon => {
                    if (depth != 0 or t == type_first) return null;
                    type_span = .{ .first = type_first, .last = t - 1 };
                    break;
                },
                else => {},
            }
        }
        if (type_span == null) return null;
        u = t;
    }
    if (u >= tags.len or tags[u] != .equal) return null;

    // Balance to the `;` that ends the declaration, so an initializer
    // containing its own blocks, parens, or semicolons is captured
    // whole.
    const init_first = u + 1;
    var depth: u32 = 0;
    var w: Ast.TokenIndex = init_first;
    while (w < tags.len) : (w += 1) {
        switch (tags[w]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                if (depth == 0) return null;
                depth -= 1;
            },
            .semicolon => {
                if (depth != 0) continue;
                if (w == init_first) return null;
                return .{ .type = type_span, .init = .{ .first = init_first, .last = w - 1 } };
            },
            else => {},
        }
    }
    return null;
}

/// True when any token in `span` opens a brace — i.e. the span builds
/// a VALUE, not a bare type.  `const V = [4]u8;` names the type;
/// `const V = [4]u8{ … };` names a pointer to one, and only the first
/// describes what `var v: V` stores.
fn spanHasBrace(tree: *const Ast, span: TokenSpan) bool {
    const tags = tree.tokens.items(.tag);
    if (span.first > span.last or span.last >= tags.len) return false;
    var t: Ast.TokenIndex = span.first;
    while (t <= span.last) : (t += 1) {
        if (tags[t] == .l_brace) return true;
    }
    return false;
}

/// Token span of the initializer that follows the `=` at `eq_tok` in a
/// `var|const <name>: <T> = <init>;` declaration — everything up to
/// the `;` that ends it at depth zero, so an initializer carrying its
/// own braces, brackets, parens or semicolons comes back whole.  Null
/// when the declaration ends without one, or when the delimiters do
/// not balance.
fn initSpanAfter(tree: *const Ast, eq_tok: Ast.TokenIndex) ?TokenSpan {
    const tags = tree.tokens.items(.tag);
    if (eq_tok + 1 >= tags.len) return null;
    const first = eq_tok + 1;
    var depth: u32 = 0;
    var t = first;
    while (t < tags.len) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                if (depth == 0) return null;
                depth -= 1;
            },
            .semicolon => {
                if (depth != 0) continue;
                if (t == first) return null;
                return .{ .first = first, .last = t - 1 };
            },
            else => {},
        }
    }
    return null;
}

test "comptime fill: lexical memo shares a tree but separates use tokens and names" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const A = 3;
        \\fn f(p: u8) void { const B = 4; _ = A; _ = p; }
        \\fn g(q: u8) void { _ = A; _ = q; }
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = file_cache.FileCache.init(gpa, &tree);
    defer cache.deinit();
    var first = Resolver.init(gpa, &tree, &cache, null);
    defer first.deinit();
    var second = Resolver.init(gpa, &tree, &cache, null);
    defer second.deinit();
    var uses: [2]Ast.TokenIndex = undefined;
    var count: usize = 0;
    for (tree.tokens.items(.tag), 0..) |tag, raw| {
        if (tag != .identifier) continue;
        const token: Ast.TokenIndex = @intCast(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "A") or tree.tokenTag(token - 1) == .keyword_const) continue;
        uses[count] = token;
        count += 1;
    }
    try std.testing.expectEqual(uses.len, count);
    const a = first.visibleDeclAt(uses[0], "A").?;
    const b = first.visibleDeclAt(uses[0], "B").?;
    try std.testing.expect(a.name_tok != b.name_tok);
    try std.testing.expect(first.visibleDeclAt(uses[0], "missing") == null);
    try std.testing.expect(first.visibleDeclAt(uses[1], "B") == null);
    try std.testing.expect(first.visibleDeclAt(uses[1], "A").?.name_tok == a.name_tok);
    // A caller-owned spelling can change immediately after the query.
    var name = [_]u8{'A'};
    try std.testing.expect(first.visibleDeclAt(uses[0], &name).?.name_tok == a.name_tok);
    name[0] = 'B';
    try std.testing.expect(first.visibleDeclAt(uses[0], &name).?.name_tok == b.name_tok);
    try std.testing.expect(first.index() == second.index());
    first.deinit();
    try std.testing.expect(second.visibleDeclAt(uses[0], "A").?.name_tok == a.name_tok);
    try std.testing.expect(second.visibleDeclAt(uses[0], "B").?.name_tok == b.name_tok);
}

test "comptime fill: lexical memo does not cross trees or certify an incomplete index" {
    const gpa = std.testing.allocator;
    var one = try Ast.parse(gpa, "const A = 3; fn f() void { _ = A; }", .zig);
    defer one.deinit(gpa);
    var two = try Ast.parse(gpa, "const B = 4; fn f() void { _ = B; }", .zig);
    defer two.deinit(gpa);
    var cache = file_cache.FileCache.init(gpa, &one);
    defer cache.deinit();
    var first = Resolver.init(gpa, &one, &cache, null);
    defer first.deinit();
    var foreign = Resolver.init(gpa, &two, &cache, null);
    defer foreign.deinit();
    var token: Ast.TokenIndex = 0;
    for (one.tokens.items(.tag), 0..) |tag, raw| {
        if (tag == .identifier and std.mem.eql(u8, one.tokenSlice(@intCast(raw)), "A"))
            token = @intCast(raw);
    }
    try std.testing.expect(first.visibleDeclAt(token, "A") != null);
    try std.testing.expect(foreign.visibleDeclAt(token, "B") != null);
    try std.testing.expect(foreign.visibleDeclAt(token, "A") == null);
    try std.testing.expect(first.index() != foreign.index());
    // No prefix of a failed raw-material walk is a visibility proof.
    foreign.index().complete = false;
    try std.testing.expect(foreign.visibleDeclAt(token, "B") == null);
}

test "comptime fill: lexical memo owns absent query spellings" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "const A = 3; fn f() void { _ = A; }", .zig);
    defer tree.deinit(gpa);
    var resolver = Resolver.init(gpa, &tree, null, null);
    defer resolver.deinit();
    var token: Ast.TokenIndex = 0;
    for (tree.tokens.items(.tag), 0..) |tag, raw| {
        if (tag == .identifier and std.mem.eql(u8, tree.tokenSlice(@intCast(raw)), "A"))
            token = @intCast(raw);
    }
    var name = [_]u8{'X'};
    try std.testing.expect(resolver.visibleDeclAt(token, &name) == null);
    name[0] = 'A';
    try std.testing.expect(resolver.visibleDeclAt(token, &name) != null);
    try std.testing.expect(resolver.visibleDeclAt(token, "X") == null);
    try std.testing.expectEqual(@as(usize, 2), resolver.index().visible.count());
    var keys = resolver.index().visible.keyIterator();
    while (keys.next()) |key| {
        if (!std.mem.eql(u8, key.name, "X")) continue;
        try std.testing.expect(key.owned_name);
        try std.testing.expect(key.name.ptr != &name);
    }
}
