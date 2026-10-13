//! Detects `return identifier.items;` inside a function — returning the
//! `.items` slice of a local `ArrayList` directly leaks the backing
//! allocation: the caller receives a `[]T` slice but has no `ArrayList`
//! handle to call `.deinit()` on, so the capacity bytes are permanently
//! lost.  The correct form is `return list.toOwnedSlice()`, which transfers
//! ownership of exactly the used bytes to the caller.
//!
//! Real-world instance:
//!   - oven-sh/bun#23885 (toUTF8AllocWithType): the function built a local
//!     `var list = try std.ArrayList(u8).initCapacity(allocator, n)` and
//!     returned `list.items`.  The caller freed the returned slice via
//!     `allocator.free()`, which freed only `items.len` bytes; the extra
//!     capacity allocated by `initCapacity` leaked on every call.
//!     Fix: `return list.toOwnedSlice()`.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `keyword_return identifier period identifier("items") semicolon`
//!   — 5 tokens.  Fire at the `return` token.
//!   Suppresses `self`/`this` receivers (those access a struct field, not a
//!   local ArrayList).  `return list.toOwnedSlice()` does NOT match (ends
//!   with `l_paren` not `semicolon`).
//!
//!   One more suppression is proved in that same walk: a full-capacity
//! comparison written in the enclosing function — `assert(list.items.len
//! == list.capacity)`, in either order — says the returned slice covers the
//! whole allocation, so the caller can free it as it stands.  Both operands
//! must be THIS list's; `other.capacity == list.items.len` equates two lists
//! and proves nothing about this one.  The comparison is what is read, not
//! the mention of `.capacity`, and it is bounded by that function's own
//! tokens so no other function's can answer for it.
//!
//! Semantic suppression (the arena-backed standard list) is proved per
//! return site: the local must be declared with the standard library's
//! list type, every allocator that can reach its buffer must be arena
//! backed, and the buffer must not be released or escaped first.
//! A pointer parameter can also borrow an arena field of a foreign context:
//! resolved SDK identity proves the provider, and rejecting other pointer uses
//! prevents a reset, rebind or escape from invalidating that returned borrow.
//! A proof that cannot be completed is never read as a proof — see
//! `src/rules/misc/return-arraylist-items.md`.
//!
//! The bounded proof reuses scoped bindings and indexes each questioned
//! function's AST subtree once. Repeated declaration and capture queries do
//! not scan unrelated functions. Each node visited, lookup answered and
//! allocator expression resolved spends the unchanged file allowance in
//! `call_summary.actual_query_work_limit`. An exhausted proof propagates its
//! error and reports the return that initiated it, never a partial proof.
//!
//! One boundary of that proof is a refusal, and it is stated here rather
//! than left to be discovered.  When the arena reaches a private helper,
//! the rule must be able to say that EVERY call of that helper hands it
//! an arena-backed allocator, and that caller set is read by resolved
//! DECLARATION rather than by the spelling of a name.  A callee a file
//! can also reach BY NAME — `@field(Model, "grow")` binds the same
//! function to a fresh local, and the call through that local is spelled
//! with the LOCAL's name — is a caller that nothing reading names can
//! see, so a file that writes one is reported rather than proved.  That
//! is a statement about what this rule can read, not a claim that a
//! reflected call is unsafe, and nothing here says a reflected callee
//! would be safe either: the rule is asked about an argument it cannot
//! resolve, and an unresolved argument is not evidence.  The same
//! refusal answers every other caller set it cannot settle, and there is
//! no second, looser opinion behind it.
//!
//! Each closed call maps the exact declared formal to its actual expression.
//! An instance call and an unbound method call can reach the same declaration
//! with different written argument slots; the resolver settles that mapping.
//!
//! A third reading answers the memoised case: a header copied out of a
//! container the caller already owns — `if (self.memo.get(key)) |cached|
//! return cached.items;` — names bytes the container still owns, so the
//! copy dying at the `return` loses nothing.  The copy is a view, and a
//! view is only a borrow while the container, the entry inside it and
//! the header it copied are all exactly as they were found; each of
//! those is proved per site.
//!
//!   What may be written between the capture and the `return` is read from
//!   the CALLEE's own body and from what the call handed it, never from the
//!   spelling of the call.  A callee that releases nothing is quiet whatever
//!   it was handed; a callee that releases storage it was not handed is not
//!   quiet for any argument at all; and a callee that releases what one of
//!   its formals names is quiet only while nothing this call passed it is the
//!   receiver's own storage.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_model = @import("../../model/file_model.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const resolver_mod = @import("../../type_resolver.zig");
const tokens = @import("../../ast/tokens.zig");
const budget_mod = @import("../../budget.zig");
const std_types = @import("../../model/std_type_query.zig");
const call_summary = @import("../../cache/call_summary.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "return-arraylist-items";

/// The errors the arena proof's walks raise, named rather than inferred.
///
/// Those walks call each other in a cycle: `allocatorExprIsSafe`
/// answers a helper's parameter, `identifierAllocatorIsSafe` answers a
/// name's initializer and that helper's callers, and `allCallsUseArena`
/// comes back to `allocatorExprIsSafe` for each argument it reads —
/// along the same edges `contextFieldAllocatorIsSafe` and
/// `callbackRegistrationHasContext` take.  Inferred error sets are
/// settled in dependency order, so a cycle has no order to be settled
/// in, and leaving these inferred is what makes their error contract
/// unspecified rather than merely unwritten.
///
/// Allocation, file-model and budget failures propagate through the proof.
/// So do SDK lookup errors: cancellation, source exclusion and unsupported
/// URI schemes. A failed model or index is not evidence that a declaration
/// is absent.
const ProofError = file_cache_mod.SummaryError;

/// Levels of allocator-expression recursion one arena proof may descend: a
/// local initialised from a local initialised from a parameter whose
/// callers pass a local, and so on.  A chain longer than this is
/// not an answer in either direction, so the proof raises
/// `error.AnalysisBudgetExceeded` instead of returning a value.
const allocator_depth_limit: u8 = 16;

/// Declaration hops `reachesReceiverStorage` may follow from a handed-over
/// value to the receiver's own storage.  Same contract as above.
const receiver_depth_limit: u8 = 8;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .return_arraylist_items)) return;

    // Both suppression proofs ask the same declaration questions, and the
    // arena proof asks them once per growth site and once per level of its
    // recursion.  One index, built on the first question rather than for a
    // file that never asks one, answers all of them and dies with this
    // call; it also carries the step budget that bounds the asking.
    var remaining: u32 = call_summary.actual_query_work_limit;
    var index = DeclIndex.init(gpa, tree, cache, &remaining);
    defer index.deinit();

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var return_tok: Ast.TokenIndex = 0;
    while (return_tok + 4 <= last_tok) : (return_tok += 1) {
        // Pattern: return identifier . items ;
        if (tags[return_tok] != .keyword_return) continue;
        if (tags[return_tok + 1] != .identifier) continue;
        if (tags[return_tok + 2] != .period) continue;
        if (tags[return_tok + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(return_tok + 3), "items")) continue;
        if (tags[return_tok + 4] != .semicolon) continue;

        // Suppress self/this — those access a struct field, not a local ArrayList.
        const recv = tree.tokenSlice(return_tok + 1);
        if (std.mem.eql(u8, recv, "self") or std.mem.eql(u8, recv, "this")) continue;

        // Scope lookup uses the resolver's existing document index when present.
        const fn_decl = if (cache.zls) |resolver|
            try resolver.enclosingFunctionAt(return_tok)
        else
            tokens.enclosingFnDecl(tree, return_tok);
        index.return_token = return_tok;

        // Suppress when this function proves the list's whole capacity is in
        // use — `assert(list.items.len == list.capacity)`.
        if (capacityFullyUsed(tree, fn_decl, return_tok, recv)) continue;

        if (fn_decl) |decl| {
            if (recvIsPointerParam(tree, decl, recv)) continue;
        }

        // A capture cannot be a locally allocated header. Resolve its owner
        // before asking an arena proof about declarations or growth sites.
        if (try returnsBorrowedContainerValue(tree, cache, &index, fn_decl, return_tok, recv)) continue;

        // Unknown allocator origins still refuse this proof.
        if (try listUsesArenaBackedAllocator(tree, cache, &index, fn_decl, return_tok, recv)) continue;

        try report(gpa, problems, tree, return_tok);
    }
}

/// True when the function the return is written in equates this list's used
/// length with its own capacity before that return — `assert(list.items.len ==
/// list.capacity)` in either order, or the same comparison standing as the
/// return's guard.  Both operands must be THIS list's: `other.capacity ==
/// list.items.len` equates two different lists and proves nothing about what
/// this one covers.  Then the returned slice covers the whole allocation and
/// the caller can free it as-is.
///
/// The COMPARISON is what is read, not the mere mention of `.capacity`: a size
/// read for a log line, or a `capacity > 4` test, says nothing about how much
/// of the buffer the returned slice covers, and neither is the statement this
/// suppression exists for.  The scan is bounded by the enclosing function,
/// so a comparison in some other function cannot answer for this one — the
/// same bound the arena proof walks inside.
fn capacityFullyUsed(
    tree: *const Ast,
    fn_decl: ?Ast.Node.Index,
    return_tok: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const decl = fn_decl orelse return false;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(decl);
    // The two operands are different widths — `recv . items . len` is
    // five tokens and `recv . capacity` is three — so each orientation is
    // read at the offset its own operand is written at.  A single shared
    // offset only holds for the operand it was measured on: reading the
    // shorter one five tokens back asks about the tokens standing in
    // front of the operator rather than about the operand, and the
    // reverse comparison then reads as though it had no proof in it.
    // Each orientation reads a different distance ahead of the operator —
    // four tokens for `recv . capacity`, six for `recv . items . len` — so
    // each is bounded by its own.  A bound narrower than the widest read
    // drops the comparison written as the `return`'s own guard, which is
    // the one place the two operands sit closest to the `return` there is:
    // `if (list.items.len == list.capacity) return list.items;` puts the
    // operator five tokens in front of it.
    var t = first;
    while (t + 5 <= return_tok) : (t += 1) {
        if (tags[t] != .equal_equal) continue;
        if (t < first + 5) continue;
        if (isListLengthAt(tree, t - 5, recv) and isListCapacityAt(tree, t + 1, recv)) {
            if (capacityHoldsAt(tree, first, t + 4, return_tok, recv)) return true;
        }
        if (t + 6 <= return_tok and
            isListCapacityAt(tree, t - 3, recv) and isListLengthAt(tree, t + 1, recv))
        {
            if (capacityHoldsAt(tree, first, t + 6, return_tok, recv)) return true;
        }
    }
    return false;
}

/// True when nothing between the comparison's last operand and the
/// `return` keyword can have moved the header the comparison settled.
///
/// EVERY mention of the receiver in that window refuses the proof.  A
/// growth entry point moves the buffer, a release frees it, a rebind
/// points it elsewhere, a write through `.items` replaces it, and handing
/// `recv.items` to a callee lets that callee free or realloc what it was
/// given — none of which the comparison survives.  There is no read of
/// this receiver that needs allowing: the slice the `return` itself names
/// is written AFTER the `return` keyword, so it is outside the window by
/// construction rather than by an exception carved out of it.
///
/// The question is asked about this receiver and about nothing else, so
/// another list growing in the same function does not void a proof about
/// this one — that shows up as a name this scan is not looking for.
fn capacityHoldsAt(
    tree: *const Ast,
    fn_first: Ast.TokenIndex,
    resume_token: Ast.TokenIndex,
    return_tok: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t = resume_token;
    while (t < return_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        return false;
    }
    // A `const` bound BEFORE the comparison to something that mentions
    // this receiver is a second name for its header or for the bytes
    // behind it, and a mutation written through that name is invisible to
    // the scan above — that scan only knows the name this question is
    // about.  No attempt is made to classify WHICH of the three it is:
    // `&recv`, `recv.items` and `recv` are all refusals, because deciding
    // that one of them is harmless is the very proof this rule does not
    // have.  With no such binding, another list's growth is still this
    // proof's own business as little as it ever was.
    return !receiverEscapes(tree, fn_first, resume_token, recv);
}

/// A `const` or `var` written in `[from, to)` whose own initializer
/// mentions `recv` — the one shape that makes a second name for this
/// header, or for its backing slice, exist before the comparison.
///
/// This reads the binding rather than the whole window, which is what
/// keeps it from swallowing the ordinary `fill(&list)` call: an argument
/// is not a second name this file can read.  What it cannot do is prove
/// such a name harmless, and it does not try.
fn receiverEscapes(
    tree: *const Ast,
    from: Ast.TokenIndex,
    to: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t = from;
    while (t + 2 < to) : (t += 1) {
        if (tags[t] != .keyword_const and tags[t] != .keyword_var) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        // The initializer runs to the statement's own semicolon, so one
        // binding cannot answer for the next one's tokens.
        var v = t + 3;
        while (v < to) : (v += 1) {
            if (tags[v] == .semicolon) break;
            if (tags[v] != .identifier) continue;
            if (std.mem.eql(u8, tree.tokenSlice(v), recv)) return true;
        }
    }
    return false;
}

/// `recv . items . len` written at `token`.
fn isListLengthAt(tree: *const Ast, token: Ast.TokenIndex, recv: []const u8) bool {
    return tokenIsNamed(tree, token, recv) and
        tree.tokenTag(token + 1) == .period and
        tokenIsNamed(tree, token + 2, "items") and
        tree.tokenTag(token + 3) == .period and
        tokenIsNamed(tree, token + 4, "len");
}

/// `recv . capacity` written at `token`.
fn isListCapacityAt(tree: *const Ast, token: Ast.TokenIndex, recv: []const u8) bool {
    return tokenIsNamed(tree, token, recv) and
        tree.tokenTag(token + 1) == .period and
        tokenIsNamed(tree, token + 2, "capacity");
}

/// A receiver chain: the root name plus the field names walked after it,
/// in source order.  The two walks in this file that build a chain hand the
/// rest of the proof this one shape, and a chain is only ever built through
/// `push` and compared through `startsWith` — so how long a chain may be,
/// and what counts as reaching one, are one answer rather than one per walk.
const ProofPath = struct {
    root: []const u8,
    segments: [8][]const u8 = undefined,
    len: usize = 0,

    /// Append one field name to the chain.  Every walk that builds a path
    /// goes through here, so how long a chain may be and what a chain that
    /// outgrew it answers are decided once instead of in each walk.
    fn push(self: *ProofPath, name: []const u8) bool {
        if (self.len == self.segments.len) return false;
        self.segments[self.len] = name;
        self.len += 1;
        return true;
    }

    /// True when `prefix` is this chain or a leading part of it: the same
    /// root, then the same fields in the same order.  This is the question
    /// "does this write reach the container" asks, and asking it as a
    /// comparison of paths is what keeps the answer from being re-derived
    /// field by field at each call site.
    fn startsWith(self: *const ProofPath, prefix: *const ProofPath) bool {
        if (prefix.len > self.len) return false;
        if (!std.mem.eql(u8, self.root, prefix.root)) return false;
        var i: usize = 0;
        while (i < prefix.len) : (i += 1) {
            if (!std.mem.eql(u8, self.segments[i], prefix.segments[i])) return false;
        }
        return true;
    }
};

const AggregateRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// What the walk proved about every allocator that can move a local list's
/// backing buffer before the `return`.
///   `none`     — no such allocator was reached, so nothing was proved
///   `arena`    — every one of them is arena-backed
///   `unproven` — at least one is not, which voids the suppression
const Growth = enum { none, arena, unproven };

/// Fold one observed operation into the walk's verdict.
fn noteGrowth(current: *Growth, seen: Growth) void {
    if (seen == .unproven) {
        current.* = .unproven;
    } else if (current.* == .none) {
        current.* = .arena;
    }
}

/// What the field scan saw: every write this file makes to one context
/// field, and how many of those carried an allocator the proof can
/// account for.
///
/// The two counts are ONE question — was EVERY write safe? — and the
/// verdict lives in `allSafe`, so no caller reaches the answer from one
/// of the counts by itself.
const WriteTally = struct {
    writes: usize = 0,
    safe_writes: usize = 0,

    /// Record one write to the field, and whether its value was proved.
    /// A write this scan could not read is recorded as UNSAFE: it is a
    /// write the file makes and no proof accounts for, which is exactly
    /// what the verdict below has to see.
    fn record(self: *WriteTally, safe: bool) void {
        self.writes += 1;
        if (safe) self.safe_writes += 1;
    }

    /// True when the field was written at least once and every one of
    /// those writes was safe.  A field this file never writes says
    /// nothing about what its readers are handed, so it refuses.
    fn allSafe(self: WriteTally) bool {
        return self.writes != 0 and self.writes == self.safe_writes;
    }
};

/// One local declaration, recorded under the token its NAME is written at.
/// That token is the declaration's identity inside a function: it orders two
/// declarations of one name for shadowing, and it is the reference point a
/// lookup filters on, so answering a question never has to re-read the
/// declaration's own tokens to decide which of them was in scope.
const IndexedDecl = struct {
    name_token: Ast.TokenIndex,
    type_node: Ast.Node.OptionalIndex,
    init_node: Ast.Node.OptionalIndex,
};

/// Where one function's declarations sit in the shared index.  A function's
/// first token identifies it: SIBLING functions' token spans cannot
/// interleave, so it is also what keeps one function's declarations from
/// answering for another's — no entry is ever cached by spelling alone.
/// A NESTED function shares its parent's span and is reached through it on
/// purpose, which is what keeps a nested declaration of the same name a
/// refusal rather than a grant.
const IndexedFn = struct {
    first_token: Ast.TokenIndex,
    first: usize,
    count: usize,
};

/// A range-filtered pass over an already indexed function subtree. AST node
/// numbers need not follow token order; the subtree supplies the node set.
const NodeScan = struct {
    tree: *const Ast,
    index: *DeclIndex,
    nodes: []const Ast.Node.Index,
    from: Ast.TokenIndex,
    to: Ast.TokenIndex,
    cursor: usize = 0,

    fn next(self: *NodeScan) ProofError!?Ast.Node.Index {
        while (self.cursor < self.nodes.len) {
            const node = self.nodes[self.cursor];
            self.cursor += 1;
            try self.index.spend(self.tree.nodeMainToken(node));
            const node_first = self.tree.firstToken(node);
            if (node_first < self.from or node_first > self.to) continue;
            return node;
        }
        return null;
    }
};

/// The declarations this file's arena proof asks about, and the budget that
/// bounds the asking.
///
/// The question is "which declaration of this name is in scope at this token,
/// inside this function", and it comes once per growth site and once per
/// level of the proof's recursion.  Answering it by walking every node of
/// the file again is what made the proof cost the file's node count per
/// question.  A function is walked ONCE — the first time anything asks
/// about it — and every later question about that function is answered from
/// that walk, so a file with many return sites pays for each function once
/// rather than once per site.
const DeclIndex = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    remaining: *u32,
    decls: std.ArrayListUnmanaged(IndexedDecl) = .empty,
    functions: std.ArrayListUnmanaged(IndexedFn) = .empty,
    body_nodes: std.AutoHashMapUnmanaged(Ast.Node.Index, []const Ast.Node.Index) = .empty,
    return_token: ?Ast.TokenIndex = null,

    fn init(
        gpa: std.mem.Allocator,
        tree: *const Ast,
        cache: *file_cache_mod.FileCache,
        remaining: *u32,
    ) DeclIndex {
        return .{ .gpa = gpa, .tree = tree, .cache = cache, .remaining = remaining };
    }

    fn deinit(self: *DeclIndex) void {
        self.decls.deinit(self.gpa);
        self.functions.deinit(self.gpa);
        var bodies = self.body_nodes.valueIterator();
        while (bodies.next()) |nodes| self.gpa.free(nodes.*);
        self.body_nodes.deinit(self.gpa);
    }

    /// Build only this function's body, once. The cache supplies scoped
    /// bindings; the engine iterator supplies AST children, including nested
    /// declarations. No sibling function or unrelated file node is visited.
    fn nodesOf(self: *DeclIndex, fn_decl: Ast.Node.Index) ProofError![]const Ast.Node.Index {
        try self.spend(self.tree.nodeMainToken(fn_decl));
        if (self.body_nodes.get(fn_decl)) |nodes| return nodes;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return &.{};
        const Iterator = @import("type_engine").AstIterator;
        const Frame = union(enum) {
            children: Iterator,
            switch_children: struct { condition: ?Ast.Node.Index, cases: []const Ast.Node.Index },

            fn next(frame: *@This(), tree: *const Ast) ?Ast.Node.Index {
                switch (frame.*) {
                    .children => |*children| return children.next(tree),
                    .switch_children => |*children| {
                        if (children.condition) |condition| {
                            children.condition = null;
                            return condition;
                        }
                        if (children.cases.len == 0) return null;
                        const node = children.cases[0];
                        children.cases = children.cases[1..];
                        return node;
                    },
                }
            }
        };
        var frames: std.ArrayListUnmanaged(Frame) = .empty;
        defer frames.deinit(self.gpa);
        var nodes: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        defer nodes.deinit(self.gpa);
        try frames.append(self.gpa, .{ .children = .{ .array = .{
            body.toOptional(), .none, .none, .none, .none,
        } } });
        while (frames.items.len != 0) {
            const node = frames.items[frames.items.len - 1].next(self.tree) orelse {
                frames.items.len -= 1;
                continue;
            };
            try self.spend(self.tree.nodeMainToken(node));
            try nodes.append(self.gpa, node);
            const frame: Frame = if (self.tree.fullSwitch(node)) |sw|
                .{ .switch_children = .{ .condition = sw.ast.condition, .cases = sw.ast.cases } }
            else
                .{ .children = Iterator.init(self.tree, node) };
            try frames.append(self.gpa, frame);
        }
        const owned = try nodes.toOwnedSlice(self.gpa);
        errdefer self.gpa.free(owned);
        try self.body_nodes.put(self.gpa, fn_decl, owned);
        return owned;
    }

    fn scanNodes(
        self: *DeclIndex,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ProofError!NodeScan {
        return .{
            .tree = self.tree,
            .index = self,
            .nodes = try self.nodesOf(fn_decl),
            .from = first,
            .to = last,
        };
    }

    /// Charge real work, keeping the initiating return as the failure site.
    fn spend(self: *DeclIndex, token: Ast.TokenIndex) !void {
        if (self.remaining.* == 0)
            return giveUp(self.tree, self.return_token orelse token);
        self.remaining.* -= 1;
    }

    /// The proof would have to descend past `cap` levels to answer.  The
    /// failure is recorded at the initiating return, like `spend`.
    fn tooDeep(self: *DeclIndex, token: Ast.TokenIndex, cap: u8) (budget_mod.BudgetError || error{SourceTooWide}) {
        return stopAt(self.tree, self.return_token orelse token, .arena_proof_depth, cap);
    }

    /// The declaration of `name` that a USE written at `use_token` names,
    /// or null when no declaration is in scope there.
    ///
    /// The scope is what decides, and it is read from the cache's own
    /// `LocalBindings` at the exact token of the use.  Answering instead
    /// by "the last declaration of this name written before that token"
    /// ignores WHERE it was written: a local declared inside a block that
    /// has since closed still read as in scope, so a header allocated
    /// from an arena local that died before the return was reached
    /// through a name the walk still believed was live.  `findAt` holds
    /// every binding to the block it was written in, so an ended one is
    /// not a candidate and a shadowing local still wins over what it
    /// shadows.
    fn lookup(
        self: *DeclIndex,
        fn_decl: Ast.Node.Index,
        name: []const u8,
        use_token: Ast.TokenIndex,
    ) !?IndexedDecl {
        // Charged before anything is looked at, so the scope fix did not
        // buy its answer for free: everything below either reads the
        // declaration index or walks the bindings.
        try self.spend(use_token);
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return null;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
        // A failed binding query cannot justify falling through to another
        // scope. Propagate the failure instead of treating it as no local.
        const bindings = try self.cache.localBindings(proto, body);
        // `findAt` is a linear pass over the body's bindings, so the pass
        // is charged before it runs rather than after it succeeded.  The
        // site is the use the question was asked at, which is what the
        // diagnostic can point at.
        var scanned = bindings.items.len;
        while (scanned > 0) : (scanned -= 1) try self.spend(use_token);
        const binding = bindings.findAt(name, use_token) orelse return null;
        // Parameters and payloads cannot name a locally declared list. Do not
        // index declarations for a question that the scoped binding settles.
        if (binding.origin == .param or binding.origin == .loop_capture) return null;
        const name_token = binding.name_token;
        const indexed = try self.indexOf(fn_decl);
        // The binding names the declaration; the index carries the nodes
        // that declaration was written with, keyed by the very token its
        // NAME is at.  A parameter and a loop capture bind a name without
        // a `var_decl` this walk indexed, so their name token matches no
        // entry and they answer null — which is the refusal they are
        // worth: a receiver handed in as a parameter is not a local whose
        // buffer this proof can account for.
        var i: usize = indexed.first;
        const end = indexed.first + indexed.count;
        while (i < end) : (i += 1) {
            const entry = self.decls.items[i];
            try self.spend(entry.name_token);
            if (entry.name_token == name_token) return entry;
        }
        return null;
    }

    /// The declarations of `fn_decl`, walking its own nodes the first time
    /// and answering from that walk ever since.
    fn indexOf(self: *DeclIndex, fn_decl: Ast.Node.Index) !IndexedFn {
        const first_token = self.tree.firstToken(fn_decl);
        for (self.functions.items) |entry| {
            // The table is a linear pass too, and a hit on the last entry
            // cost as much as a miss on the first.
            try self.spend(first_token);
            if (entry.first_token == first_token) return entry;
        }
        const start = self.decls.items.len;
        // A build that runs out of budget leaves NOTHING behind: the
        // entries appended since `start` are rolled back, so a later
        // question re-walks this function from a clean range instead of
        // reading a half-built one as if it were whole.
        errdefer self.decls.shrinkRetainingCapacity(start);
        const body = tokens.bodyOf(self.tree, fn_decl);
        if (body) |node| {
            const body_first = self.tree.firstToken(node);
            const fn_last = self.tree.lastToken(fn_decl);
            const tags = self.tree.tokens.items(.tag);
            var scan = try self.scanNodes(fn_decl, body_first, fn_last);
            while (try scan.next()) |candidate| {
                switch (self.tree.nodeTag(candidate)) {
                    .local_var_decl, .simple_var_decl, .aligned_var_decl => {},
                    else => continue,
                }
                const decl = self.tree.fullVarDecl(candidate) orelse continue;
                const name_token = decl.ast.mut_token + 1;
                // A fn's tokens are contiguous and a sibling's cannot
                // interleave, so the span rejects declarations of other
                // functions without reading their declarations at all.
                if (name_token < body_first or name_token > fn_last or
                    name_token >= tags.len or tags[name_token] != .identifier)
                    continue;
                try self.decls.append(self.gpa, .{
                    .name_token = name_token,
                    .type_node = decl.ast.type_node,
                    .init_node = decl.ast.init_node,
                });
            }
        }
        const indexed: IndexedFn = .{
            .first_token = first_token,
            .first = start,
            .count = self.decls.items.len - start,
        };
        try self.functions.append(self.gpa, indexed);
        return indexed;
    }
};

/// Record the bound the arena proof hit — the cap, how far the counter got,
/// the site it was on and the function that site is written in — and return
/// the error every bounded walk propagates.  A caller that swallows the
/// error still knows from the record why the file was skipped.
///
/// The cap is READ rather than passed.  Every step-counted walk this rule
/// bounds spends the one allowance `call_summary.actual_query_work_limit`
/// names; the depth bounds go through `DeclIndex.tooDeep`.
fn giveUp(tree: *const Ast, token: Ast.TokenIndex) (budget_mod.BudgetError || error{SourceTooWide})!void {
    return stopAt(tree, token, .arena_proof_steps, call_summary.actual_query_work_limit);
}

/// Shared recorder behind `giveUp` and `DeclIndex.tooDeep`: every bound is
/// checked before it is used, so the value a tripped bound reached is the
/// bound itself.
fn stopAt(
    tree: *const Ast,
    token: Ast.TokenIndex,
    limit: budget_mod.Limit,
    cap: u32,
) (budget_mod.BudgetError || error{SourceTooWide}) {
    var name: budget_mod.NameBuf = .{};
    if (tokens.enclosingFnDecl(tree, token)) |decl| {
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(tree, &buffer, decl)) |proto| {
            if (proto.name_token) |name_tok| name.set(tree.tokenSlice(name_tok));
        }
    }
    const site = try Pos.fromTokenStart(tree, token);
    return budget_mod.fail(.{
        .limit = limit,
        .limit_value = cap,
        .reached = cap,
        .byte = site.byte,
        .document = budget_mod.documentForTree(tree),
        .line = site.line,
        .column = site.column,
        .function = name,
    });
}

const ArenaProof = struct {
    tree: *const Ast,
    model: *const file_model.FileModel,
    cache: *file_cache_mod.FileCache,
    index: *DeclIndex,

    fn listUsesArena(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        return_tok: Ast.TokenIndex,
        list_name: []const u8,
    ) ProofError!bool {
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;
        const body_first = self.tree.firstToken(body);
        // The proof is about the standard list's buffer.  A project type
        // with an allocator-taking `append`, or a file-local type that
        // merely reuses the name, owns whatever its `.items` names instead,
        // so an unproved declaration is not a proof.
        if (!try self.localIsStandardList(fn_decl, list_name, return_tok)) return false;

        // One traversal of the function's own nodes, and only of those: a
        // sibling function's token span cannot interleave with this one,
        // so the range both rejects another function's nodes and ends the
        // walk at this one's last token.  Every node it inspects is
        // charged, so this traversal is bounded by the cap and reported
        // at the site that reached it rather than running to whatever the
        // file's node count happens to be.
        // A nested fn's nodes fall inside that span; they can only match
        // on this same name, and a match refuses the suppression rather
        // than granting it.
        const fn_last = @min(self.tree.lastToken(fn_decl), return_tok - 1);
        var growth: Growth = .none;

        var scan = try self.index.scanNodes(fn_decl, body_first, fn_last);
        while (try scan.next()) |node| {
            switch (self.tree.nodeTag(node)) {
                .@"asm", .asm_simple, .asm_input, .asm_output => return false,
                .call, .call_comma, .call_one, .call_one_comma => {
                    var call_buf: [1]Ast.Node.Index = undefined;
                    const call = self.tree.fullCall(&call_buf, node) orelse continue;
                    const callee = fieldCallee(self.tree, call.ast.fn_expr) orelse continue;
                    if (self.tree.nodeTag(callee.receiver) != .identifier) continue;
                    if (!std.mem.eql(
                        u8,
                        self.tree.tokenSlice(self.tree.nodeMainToken(callee.receiver)),
                        list_name,
                    )) continue;
                    const method = self.tree.tokenSlice(callee.method);
                    if (listReleasesBuffer(method)) return false;
                    if (!listGrowthMethod(method)) continue;
                    noteGrowth(&growth, try self.chargeGrowth(fn_decl, call.ast.params));
                },
                .local_var_decl, .simple_var_decl, .aligned_var_decl => {
                    const decl = self.tree.fullVarDecl(node) orelse continue;
                    const name_token = decl.ast.mut_token + 1;
                    if (name_token >= return_tok or
                        !std.mem.eql(u8, self.tree.tokenSlice(name_token), list_name))
                        continue;
                    const init_node = decl.ast.init_node.unwrap() orelse continue;
                    var call_buf: [1]Ast.Node.Index = undefined;
                    const call = self.tree.fullCall(
                        &call_buf,
                        unwrapTry(self.tree, init_node),
                    ) orelse continue;
                    // The declaration already proved the TYPE, so the
                    // initializer alone decides who owns the buffer —
                    // and it is spelled both ways: `Type.constructor(…)`
                    // is a field access, `.constructor(…)` is an enum
                    // literal carrying the same name.
                    const constructor = switch (self.tree.nodeTag(call.ast.fn_expr)) {
                        .field_access => self.tree.tokenSlice(
                            fieldCallee(self.tree, call.ast.fn_expr).?.method,
                        ),
                        .enum_literal, .identifier => self.tree.tokenSlice(
                            self.tree.nodeMainToken(call.ast.fn_expr),
                        ),
                        else => continue,
                    };
                    if (listTakesForeignBuffer(constructor)) return false;
                    if (!isListConstructor(constructor)) continue;
                    noteGrowth(&growth, try self.chargeGrowth(fn_decl, call.ast.params));
                },
                .assign => {
                    // `out = …` rebinds the header, so from here on the
                    // right-hand side decides whose allocation `.items`
                    // names.  Only a literal header is known to own nothing.
                    const lhs, const rhs = self.tree.nodeData(node).node_and_node;
                    if (self.tree.nodeTag(lhs) != .identifier) continue;
                    if (!std.mem.eql(
                        u8,
                        self.tree.tokenSlice(self.tree.nodeMainToken(lhs)),
                        list_name,
                    )) continue;
                    switch (self.tree.nodeTag(rhs)) {
                        .enum_literal,
                        .struct_init_dot,
                        .struct_init_dot_comma,
                        .struct_init_dot_two,
                        .struct_init_dot_two_comma,
                        => continue,
                        .struct_init, .struct_init_comma => {
                            if (!isStandardListLiteral(self.cache, self.tree, rhs)) return false;
                        },
                        else => {
                            var call_buf: [1]Ast.Node.Index = undefined;
                            const call = self.tree.fullCall(
                                &call_buf,
                                unwrapTry(self.tree, rhs),
                            ) orelse return false;
                            const callee = fieldCallee(
                                self.tree,
                                call.ast.fn_expr,
                            ) orelse return false;
                            const constructor = self.tree.tokenSlice(callee.method);
                            if (listTakesForeignBuffer(constructor)) return false;
                            if (!isListConstructor(constructor)) return false;
                            noteGrowth(&growth, try self.chargeGrowth(fn_decl, call.ast.params));
                        },
                    }
                },
                .address_of => {
                    // `&list` hands the header itself to a callee, and
                    // nothing inside this function can prove what that
                    // callee rebinds it to.
                    const operand = self.tree.nodeData(node).node;
                    if (self.tree.nodeTag(operand) != .identifier) continue;
                    if (!std.mem.eql(
                        u8,
                        self.tree.tokenSlice(self.tree.nodeMainToken(operand)),
                        list_name,
                    )) continue;
                    return false;
                },
                else => {},
            }
        }
        return growth == .arena;
    }

    /// The allocator argument of one allocator-taking list operation: its
    /// first parameter, which every such entry point spells the same way.
    fn chargeGrowth(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        params: []const Ast.Node.Index,
    ) ProofError!Growth {
        if (params.len == 0) return .unproven;
        const arg = params[0];
        if (!(try self.allocatorExprIsSafe(
            fn_decl,
            self.tree.firstToken(arg),
            self.tree.lastToken(arg),
            0,
        ))) return .unproven;
        return .arena;
    }

    /// True when the local named `list_name` is declared with the standard
    /// library's list type.  Without an annotation the initializer names
    /// it instead: `var list = std.ArrayList(u8).initCapacity(…)`.
    fn localIsStandardList(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        list_name: []const u8,
        before: Ast.TokenIndex,
    ) ProofError!bool {
        const decl = (try self.index.lookup(fn_decl, list_name, before)) orelse return false;
        if (decl.type_node.unwrap()) |type_node| {
            if (self.cache.zls) |resolver| {
                try self.index.spend(self.tree.nodeMainToken(type_node));
                return try actualStandardList(resolver, self.index, type_node);
            }
            return isStandardListType(self.cache, self.tree, self.tree.firstToken(type_node), self.tree.lastToken(type_node));
        }
        const init = decl.init_node.unwrap() orelse return false;
        return self.initNamesStandardList(unwrapTry(self.tree, init));
    }

    fn initNamesStandardList(self: *const ArenaProof, init: Ast.Node.Index) bool {
        switch (self.tree.nodeTag(init)) {
            .struct_init, .struct_init_comma => return isStandardListLiteral(self.cache, self.tree, init),
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => return false,
        }
        var call_buf: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&call_buf, init) orelse return false;
        const callee = fieldCallee(self.tree, call.ast.fn_expr) orelse return false;
        if (!isListConstructor(self.tree.tokenSlice(callee.method))) return false;
        return isStandardListType(
            self.cache,
            self.tree,
            self.tree.firstToken(callee.receiver),
            self.tree.lastToken(callee.receiver),
        );
    }

    fn allocatorExprIsSafe(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        depth: u8,
    ) ProofError!bool {
        if (first > last) return false;
        // One step per allocator expression the proof resolves.  This is the
        // recursion the walk spends its budget on, so it is charged at the
        // level that recurses rather than only at the growth site that
        // started it.
        try self.index.spend(first);
        const tags = self.tree.tokens.items(.tag);
        var start = first;
        var end = last;
        while (start < end and tags[start] == .l_paren and tags[end] == .r_paren) {
            const close = tokens.matchParen(tags, start, end) orelse break;
            if (close != end) break;
            start += 1;
            end -= 1;
        }
        if (try self.isArenaAllocatorCall(fn_decl, start, end)) return true;
        if (start == end and tags[start] == .identifier) {
            // The only step that recurses by depth: a name is answered by
            // what it was initialised from.  Cutting that short is not
            // "unproven", it is unfinished.
            if (depth >= allocator_depth_limit) return self.index.tooDeep(start, allocator_depth_limit);
            return try self.identifierAllocatorIsSafe(fn_decl, start, depth + 1);
        }
        if (start + 2 == end and tags[start] == .identifier and
            tags[start + 1] == .period and tags[start + 2] == .identifier)
        {
            return try self.contextFieldAllocatorIsSafe(fn_decl, start, end);
        }
        return false;
    }

    fn isArenaAllocatorCall(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ProofError!bool {
        const tags = self.tree.tokens.items(.tag);
        if (first > last or tags[first] != .identifier) return false;
        var path: ProofPath = .{ .root = self.tree.tokenSlice(first) };
        var t = first;
        while (true) {
            if (t + 2 > last or tags[t + 1] != .period or
                tags[t + 2] != .identifier)
                return false;
            const segment = self.tree.tokenSlice(t + 2);
            if (t + 3 <= last and tags[t + 3] == .l_paren) {
                if (!std.mem.eql(u8, segment, "allocator")) return false;
                return t + 4 <= last and tags[t + 4] == .r_paren and
                    t + 4 == last and try self.pathIsArenaObject(fn_decl, &path, first);
            }
            if (!path.push(segment)) return false;
            t += 2;
        }
    }

    fn identifierAllocatorIsSafe(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        name_token: Ast.TokenIndex,
        depth: u8,
    ) ProofError!bool {
        const name = self.tree.tokenSlice(name_token);
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;
        try self.index.spend(name_token);
        const bindings = try self.cache.localBindings(proto, body);
        for (bindings.items) |_| try self.index.spend(name_token);
        if (bindings.findAt(name, name_token)) |binding| {
            if (binding.origin == .param) {
                var params = proto.iterate(self.tree);
                var position: usize = 0;
                while (params.next()) |param| : (position += 1) {
                    if (param.name_token != binding.name_token) continue;
                    return try self.allCallsUseArena(fn_decl, position, depth + 1);
                }
                return false;
            }
            const decl = (try self.index.lookup(fn_decl, name, name_token)) orelse return false;
            const init_node = decl.init_node.unwrap() orelse return false;
            return try self.allocatorExprIsSafe(
                fn_decl,
                self.tree.firstToken(init_node),
                self.tree.lastToken(init_node),
                depth + 1,
            );
        }
        if (self.findGlobalDecl(name)) |decl| {
            const init_node = decl.ast.init_node.unwrap() orelse return false;
            return try self.allocatorExprIsSafe(
                fn_decl,
                self.tree.firstToken(init_node),
                self.tree.lastToken(init_node),
                depth + 1,
            );
        }
        return false;
    }

    /// True when every call of `fn_decl` hands its `parameter` an
    /// arena-backed allocator, and the file is CLOSED over those calls.
    ///
    /// Closure is the whole difficulty here, and it is not answered by
    /// this file.  `FileCache.closedLocalCalls` is the only answer read:
    /// it binds each reference to the DECLARATION it resolves to rather
    /// than to the spelling of its name, it refuses reflective escapes of
    /// that declaration, and it memoises the set per declaration. An
    /// unrelated function-pointer parameter call is excluded only when the
    /// same census proves the private body cannot escape to that parameter.
    /// A helper consulted from several growth sites is resolved once.
    ///
    /// Null refuses the site, and there is no second opinion.  No
    /// resolver, no privacy, a reference that resolves elsewhere and
    /// could not be told apart from a caller, a file that reaches the
    /// callee by name — each is an argument this rule cannot resolve,
    /// and an unresolved argument is not evidence.  A name-matched
    /// census cannot stand in for the missing answer:
    /// `@field(Model, "grow")` binds the callee to a fresh local and the
    /// call through that local is spelled with the LOCAL's name, so such
    /// an entry is no identifier reference to `grow` and no call any name
    /// scan matches, and the census reads a file with a hidden heap
    /// caller as closed.
    fn allCallsUseArena(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        parameter: usize,
        depth: u8,
    ) ProofError!bool {
        if (!self.functionIsPrivate(fn_decl)) return false;
        const calls = (try self.cache.closedLocalCalls(fn_decl)) orelse return false;
        if (calls.len == 0) return false;
        const resolver = self.cache.zls orelse return false;
        const frame = resolver.resolutionFrame();
        for (calls) |node| {
            // The actual call decides whether it supplies a receiver. A
            // bound call and `Type.method(&receiver, ...)` share the same
            // formal declaration but not the same written argument slots.
            try self.index.spend(self.tree.nodeMainToken(node));
            var call_buf: [2]Ast.Node.Index = undefined;
            const arg = (try frame.callArgumentIn(&call_buf, node, parameter)) orelse return false;
            // The caller is what names the argument's own source — its
            // parameter, its local, its receiver — so the argument cannot
            // be read without it, and it must be the INNERMOST
            // declaration that spans the call: a call written inside a
            // function nested in this one is evaluated with that nested
            // function's own parameters and locals.
            //
            // The engine's own scope index already holds every function
            // declaration of this file, nested ones included, keyed by
            // the token each spans — so this is a search in what it has
            // already built, not a walk of every node for every call.  A
            // function TYPE is a different scope and is not a body a
            // call is evaluated in, so the lookup skips it.  No resolver
            // means the question is open, and an open question refuses.
            const caller = (try resolver.enclosingFunctionAt(
                self.tree.firstToken(node),
            )) orelse return false;
            if (!(try self.allocatorExprIsSafe(
                caller,
                self.tree.firstToken(arg),
                self.tree.lastToken(arg),
                depth + 1,
            ))) return false;
        }
        return true;
    }

    fn functionIsPrivate(self: *const ArenaProof, fn_decl: Ast.Node.Index) bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        const name_token = proto.name_token orelse return false;
        var back = name_token;
        var scanned: usize = 0;
        while (back > 0 and scanned < 4) : (scanned += 1) {
            back -= 1;
            if (self.tree.tokenTag(back) == .keyword_export) return false;
        }
        const name = self.tree.tokenSlice(name_token);
        if (self.declaredOwnerOf(fn_decl)) |owner| {
            const method = owner.findMethod(name) orelse return false;
            return !method.is_pub;
        }
        for (self.model.fns) |function| {
            if (function.fn_decl == fn_decl) return !function.is_pub;
        }
        return false;
    }

    /// The DECLARED container of `fn_decl`, or null when the fn is one
    /// of the file's own top-level functions rather than a method of
    /// something this file declares.
    ///
    /// `file_model.buildWithPath` synthesizes one `TypeInfo` for a whole
    /// file that writes `@This()` within its first tokens: that type's
    /// body span is `0..last` and its methods are the file's own
    /// top-level fns.  It is not a container those fns are declared
    /// inside — it is the file — and reading it as one makes every bare
    /// call in such a file look like a call of a method that is never
    /// called bare, and hands a receiver to a fn that has none.
    /// `collectTypesInRange` always sets a declared type's `body_first`
    /// to the `{` after `const X = struct`, which is never token zero,
    /// so that span is what tells the two apart without a new field on
    /// the model.
    fn declaredOwnerOf(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
    ) ?*const file_model.TypeInfo {
        const owner = self.model.containingTypeOf(fn_decl) orelse return null;
        if (owner.body_first == 0) return null;
        return owner;
    }

    fn identifierTypeName(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        name_token: Ast.TokenIndex,
    ) ProofError!?[]const u8 {
        const name = self.tree.tokenSlice(name_token);
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
        var params = proto.iterate(self.tree);
        while (params.next()) |param| {
            const token = param.name_token orelse continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(token), name)) continue;
            const type_node = param.type_expr orelse return null;
            return baseTypeName(self.tree, self.tree.firstToken(type_node), self.tree.lastToken(type_node));
        }
        const decl = (try self.index.lookup(fn_decl, name, name_token)) orelse return null;
        const type_node = decl.type_node.unwrap() orelse return null;
        return baseTypeName(self.tree, self.tree.firstToken(type_node), self.tree.lastToken(type_node));
    }

    fn pathIsArenaObject(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
        use_token: Ast.TokenIndex,
    ) ProofError!bool {
        // FileModel's field walk only starts from a method's own receiver.
        // A free function can borrow a pointer to an imported/nested context
        // too. The resolver settles both that root and the final arena field.
        if (try self.resolvedBorrowedArenaPath(fn_decl, path, use_token)) |answer| return answer;
        if (path.len == 0) {
            // Resolve the actual local at this use, not another block's
            // declaration or a file-scope value with the same spelling.
            // A body-local arena is not proved to outlive the returned view.
            if (try self.index.lookup(fn_decl, path.root, use_token)) |_| return false;
            if (self.pointerParameterIsArena(fn_decl, path.root)) |answer| return answer;
            const decl = self.findGlobalDecl(path.root) orelse return false;
            const type_node = decl.ast.type_node.unwrap() orelse return false;
            return isArenaType(
                self.cache,
                self.tree,
                self.tree.firstToken(type_node),
                self.tree.lastToken(type_node),
            );
        }
        const root = self.pathRootType(fn_decl, path) orelse return false;
        const leaf = walkFieldChain(self.tree, self.model, root, path) orelse return false;
        return isArenaType(self.cache, self.tree, leaf.type_first, leaf.type_last);
    }

    fn resolvedBorrowedArenaPath(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
        use_token: Ast.TokenIndex,
    ) ProofError!?bool {
        const resolver = self.cache.zls orelse return null;
        try self.index.spend(use_token);
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &buffer, fn_decl) orelse return null;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return null;
        const bindings = try self.cache.localBindings(proto, body);
        for (bindings.items) |_| try self.index.spend(use_token);
        const binding = bindings.findAt(path.root, use_token) orelse return null;
        // A pointer parameter borrows storage outside this frame. A local
        // arena or a by-value context does not prove that lifetime.
        if (binding.origin != .param) return null;
        const root = self.cache.nodeForExactSpan(use_token, use_token) orelse return null;
        const root_type = (try resolver.resolutionFrame().typeOfNode(root)) orelse return null;
        if (resolver.typeTag(root_type) != .pointer) return false;
        const last = use_token + @as(Ast.TokenIndex, @intCast(path.len * 2));
        const leaf = self.cache.nodeForExactSpan(use_token, last) orelse return null;
        const actual = (try resolver.containerOfNode(leaf)) orelse return null;
        if (!try resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/ArenaAllocator.zig")) return false;
        // Arena identity does not prove lifetime. Every use of this exact
        // arena path must derive its allocator, not reset/rebind it or retain
        // an alias. Other fields on a known receiver are separate paths.
        const foreign = path.len != 0 and self.pathRootType(fn_decl, path) == null;
        const return_token = self.index.return_token orelse return false;
        const body_first = self.tree.firstToken(body);
        const body_last = self.tree.lastToken(body);
        const end = if (return_token > body_first and return_token < body_last)
            return_token
        else
            body_last;
        var allocator_derived = false;
        var token = body_first;
        while (token < end) : (token += 1) {
            try self.index.spend(token);
            if (!tokenIsNamed(self.tree, token, path.root)) continue;
            var matched = true;
            for (path.segments[0..path.len], 0..) |segment, offset| {
                const at = token + @as(Ast.TokenIndex, @intCast(offset * 2));
                if (at + 2 >= end or self.tree.tokenTag(at + 1) != .period or
                    !tokenIsNamed(self.tree, at + 2, segment)) matched = false;
            }
            if (!matched) {
                // Constructing a fresh owned arena before its first allocator
                // use cannot release this slice. Do not mistake the assignment
                // target for an escaped receiver pointer.
                if (!foreign and !allocator_derived and token < use_token and
                    try self.freshReceiverArenaInit(fn_decl, path, token, use_token))
                    continue;
                if (foreign or token + 1 >= end or self.tree.tokenTag(token + 1) != .period)
                    return false;
                continue;
            }
            const at = token + @as(Ast.TokenIndex, @intCast(path.len * 2));
            if (at + 4 >= end or self.tree.tokenTag(at + 1) != .period or
                !tokenIsNamed(self.tree, at + 2, "allocator") or
                self.tree.tokenTag(at + 3) != .l_paren or
                self.tree.tokenTag(at + 4) != .r_paren) return false;
            token = at + 4;
            allocator_derived = true;
        }
        return true;
    }

    /// A whole-receiver initializer may create the arena before a callback's
    /// allocator is recorded. Accept only a standard arena VALUE initialized
    /// by its implicit `.init` constructor, not a pointer or a copied header.
    fn freshReceiverArenaInit(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
        token: Ast.TokenIndex,
        use_token: Ast.TokenIndex,
    ) ProofError!bool {
        if (path.len != 1 or token + 4 >= use_token) return false;
        const tags = self.tree.tokens.items(.tag);
        if (tags[token + 1] != .period_asterisk or tags[token + 2] != .equal or
            tags[token + 3] != .period or tags[token + 4] != .l_brace)
            return false;
        const owner = self.pathRootType(fn_decl, path) orelse return false;
        const field = walkFieldChain(self.tree, self.model, owner, path) orelse return false;
        if (!std_types.isType(
            self.cache,
            self.tree,
            field.type_first,
            field.type_last,
            "heap",
            "ArenaAllocator",
            .{},
        )) return false;
        const close = tokens.matchBrace(tags, token + 4, use_token - 1) orelse return false;
        const node = self.cache.nodeForExactSpan(token + 3, close) orelse return false;
        var fields: [2]Ast.Node.Index = undefined;
        const init = self.tree.fullStructInit(&fields, node) orelse return false;
        for (init.ast.fields) |value| {
            const first = self.tree.firstToken(value);
            try self.index.spend(first);
            if (first < 3 or tags[first - 3] != .period or tags[first - 1] != .equal or
                !tokenIsNamed(self.tree, first - 2, path.segments[0]))
                continue;
            var args: [1]Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&args, value) orelse return false;
            return call.ast.params.len == 1 and
                self.tree.nodeTag(call.ast.fn_expr) == .enum_literal and
                tokenIsNamed(self.tree, self.tree.nodeMainToken(call.ast.fn_expr), "init");
        }
        return false;
    }

    /// `?bool`: null when `fn_decl` declares no parameter by that name —
    /// the name is then the file's, not this function's.  False when the
    /// parameter is not a pointer to the standard arena.
    ///
    /// BY VALUE is refused on purpose: a copied header's own `deinit`
    /// frees the arena it was copied from, so the copy is not that
    /// arena and an allocator taken from it is not what the caller
    /// thinks it is.
    fn pointerParameterIsArena(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        name: []const u8,
    ) ?bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
        var params = proto.iterate(self.tree);
        while (params.next()) |param| {
            const token = param.name_token orelse continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(token), name)) continue;
            const type_node = param.type_expr orelse return false;
            if (self.tree.fullPtrType(type_node) == null) return false;
            return isArenaType(
                self.cache,
                self.tree,
                self.tree.firstToken(type_node),
                self.tree.lastToken(type_node),
            );
        }
        return null;
    }

    /// The type the root of `path` is read through: the receiver of
    /// `fn_decl`, when the receiver is the pointer `path.root` names and
    /// its declared type is that type.
    ///
    /// The declared container is asked first, then the type `file_model`
    /// synthesizes for a whole file that writes `@This()`.  That one is
    /// not a container those functions are declared inside — it is the
    /// file — but a top-level fn of such a file may still be written
    /// `fn get(self: *@This())`, and that receiver IS the file-struct.
    /// `receiverTypeMatches` is what proves it, by reading `@This()` as
    /// the lexical container; a `*Model` receiver in a file-struct file
    /// does not match it, so nothing else starts resolving through it.
    fn pathRootType(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
    ) ?*const file_model.TypeInfo {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
        const name = self.tree.tokenSlice(proto.name_token orelse return null);
        if (self.declaredOwnerOf(fn_decl)) |owner| {
            return self.receiverOwnsRoot(fn_decl, owner, name, path);
        }
        const file_owner = self.model.containingTypeOf(fn_decl) orelse return null;
        return self.receiverOwnsRoot(fn_decl, file_owner, name, path);
    }

    fn receiverOwnsRoot(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        owner: *const file_model.TypeInfo,
        name: []const u8,
        path: *const ProofPath,
    ) ?*const file_model.TypeInfo {
        const method = owner.findMethod(name) orelse return null;
        if (method.fn_decl != fn_decl) return null;
        const receiver = method.receiver orelse return null;
        if (!receiver.is_ptr or !std.mem.eql(u8, receiver.name, path.root)) return null;
        if (!self.receiverTypeMatches(fn_decl, owner)) return null;
        return owner;
    }

    fn pathFinalType(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
    ) ?*const file_model.TypeInfo {
        const root = self.pathRootType(fn_decl, path) orelse return null;
        if (path.len == 0) return root;
        const leaf = walkFieldChain(self.tree, self.model, root, path) orelse return null;
        const name = baseTypeName(self.tree, leaf.type_first, leaf.type_last) orelse
            return null;
        return self.model.findType(name);
    }

    fn receiverTypeMatches(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        owner: *const file_model.TypeInfo,
    ) bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        var params = proto.iterate(self.tree);
        const receiver = params.next() orelse return false;
        const type_node = receiver.type_expr orelse return false;
        const pointer = self.tree.fullPtrType(type_node) orelse return false;
        if (pointer.size != .one) return false;
        const child = pointer.ast.child_type;
        if (std.mem.eql(u8, self.tree.getNodeSource(child), "@This()")) return true;
        const spelling = tokens.typeNameFromTokens(self.tree, self.tree.firstToken(child), self.tree.lastToken(child)) orelse return false;
        return self.model.resolveTypeNameInScope(spelling, owner) == owner;
    }

    fn contextFieldAllocatorIsSafe(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ProofError!bool {
        const field_name = self.tree.tokenSlice(last);
        const context_name = (try self.identifierTypeName(fn_decl, first)) orelse return false;
        const context_info = self.model.findType(context_name) orelse return false;
        const field = context_info.findField(field_name) orelse return false;
        if (!isAllocatorType(self.cache, self.tree, field.type_first, field.type_last)) return false;
        if (!try self.callbackRegistrationHasContext(fn_decl, context_info)) return false;

        const tags = self.tree.tokens.items(.tag);
        // The root decl ends on the final token of the stream; scanning to
        // its last token covers the whole file without narrowing a `usize`
        // stream length into the token index type.
        const stream_end: Ast.TokenIndex = self.tree.lastToken(.root);
        var tally: WriteTally = .{};
        if (!try self.plainFieldWritesAreSafe(&tally, context_info, field_name, tags, stream_end))
            return false;
        if (!try self.aggregateFieldWritesAreSafe(&tally, context_info, field_name, tags, stream_end))
            return false;
        return tally.allSafe();
    }

    /// Tally every `x.field = value;` this file writes, and whether each
    /// value is an allocator expression the proof can discharge.
    ///
    /// False when the file's scope index is unavailable: the enclosing
    /// function of a write is what the proof is stated about, and a file
    /// that cannot name it has not answered the question.
    fn plainFieldWritesAreSafe(
        self: *const ArenaProof,
        tally: *WriteTally,
        context_info: *const file_model.TypeInfo,
        field_name: []const u8,
        tags: []const std.zig.Token.Tag,
        stream_end: Ast.TokenIndex,
    ) ProofError!bool {
        var t: Ast.TokenIndex = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (t < 3 or tags[t] != .equal or tags[t - 1] != .identifier or
                tags[t - 2] != .period or
                !std.mem.eql(u8, self.tree.tokenSlice(t - 1), field_name))
                continue;
            const resolver = self.cache.zls orelse return false;
            const owner_fn = (try resolver.enclosingFunctionAt(t)) orelse continue;
            const path = pathEndingAt(self.tree, t - 3) orelse continue;
            const owner = self.pathFinalType(owner_fn, &path) orelse continue;
            if (owner != context_info) continue;
            const value_start = t + 1;
            const semicolon = tokens.findStmtSemicolon(
                tags,
                value_start,
                stream_end,
            ) orelse {
                // The write is there but its value is not readable to
                // the end of the statement, so it counts and is not safe.
                tally.record(false);
                continue;
            };
            tally.record(semicolon > value_start and try self.allocatorExprIsSafe(
                owner_fn,
                value_start,
                semicolon - 1,
                0,
            ));
        }
        return true;
    }

    /// Tally every `x.context = .{ .field = value }` this file writes,
    /// and whether each `.field` value is an allocator expression the
    /// proof can discharge.
    ///
    /// A write whose right-hand side is not an aggregate at all reaches
    /// the same tally and is recorded unsafe: it assigns the field
    /// without this scan being able to read what it assigned.
    fn aggregateFieldWritesAreSafe(
        self: *const ArenaProof,
        tally: *WriteTally,
        context_info: *const file_model.TypeInfo,
        field_name: []const u8,
        tags: []const std.zig.Token.Tag,
        stream_end: Ast.TokenIndex,
    ) ProofError!bool {
        var t: Ast.TokenIndex = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (tags[t] != .equal or t == 0) continue;
            const lhs = pathEndingAt(self.tree, t - 1) orelse continue;
            const resolver = self.cache.zls orelse return false;
            const owner_fn = (try resolver.enclosingFunctionAt(t)) orelse continue;
            const owner = self.pathFinalType(owner_fn, &lhs) orelse continue;
            if (owner != context_info) continue;
            var open = t + 1;
            if (open < tags.len and tags[open] == .period) open += 1;
            if (open >= tags.len or tags[open] != .l_brace) {
                tally.record(false);
                continue;
            }
            const close = tokens.matchBrace(tags, open, stream_end) orelse continue;
            var u = open + 1;
            var aggregate_depth: u32 = 0;
            while (u < close) : (u += 1) {
                switch (tags[u]) {
                    .l_brace, .l_paren, .l_bracket => aggregate_depth += 1,
                    .r_brace, .r_paren, .r_bracket => aggregate_depth -|= 1,
                    else => {},
                }
                if (aggregate_depth != 0 or tags[u] != .identifier or
                    !std.mem.eql(u8, self.tree.tokenSlice(u), field_name))
                    continue;
                if (u == 0 or tags[u - 1] != .period or u + 1 >= close or
                    tags[u + 1] != .equal)
                    continue;
                const value_start = u + 2;
                const value_end = aggregateFieldEnd(tags, value_start, close);
                tally.record(value_end > value_start and try self.allocatorExprIsSafe(
                    owner_fn,
                    value_start,
                    value_end - 1,
                    0,
                ));
            }
            t = close;
        }
        return true;
    }

    fn callbackRegistrationHasContext(
        self: *const ArenaProof,
        callback_fn: Ast.Node.Index,
        context_info: *const file_model.TypeInfo,
    ) ProofError!bool {
        if (!self.functionIsPrivate(callback_fn)) return false;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, callback_fn) orelse return false;
        const callback_token = proto.name_token orelse return false;
        const callback_name = self.tree.tokenSlice(callback_token);
        const tags = self.tree.tokens.items(.tag);
        const last_tok: Ast.TokenIndex = self.tree.lastToken(.root);
        var references: usize = 0;
        // References arrive in token order, so the enclosing aggregate of
        // one that lands inside the aggregate already resolved is that same
        // one: carry it instead of walking the brace structure again per
        // reference.
        var enclosing: ?AggregateRange = null;
        var t: Ast.TokenIndex = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (tags[t] != .identifier or
                !std.mem.eql(u8, self.tree.tokenSlice(t), callback_name) or
                t == callback_token)
                continue;
            if (t + 1 < tags.len and (tags[t + 1] == .colon or
                (t > 0 and tags[t - 1] == .period and tags[t + 1] == .equal)))
                continue;
            references += 1;
            // The `t - 1` / `t - 2` reads below need three tokens of
            // context.  The precondition is its own statement so it is
            // established before the pattern match it protects, instead of
            // hiding as the leading term of a four-way disjunction.
            if (t < 3) return false;
            if (tags[t - 3] != .period or
                !std.mem.eql(u8, self.tree.tokenSlice(t - 2), "candidates") or
                tags[t - 1] != .equal)
                return false;
            var reused: ?AggregateRange = null;
            if (enclosing) |range| {
                if (t <= range.last) reused = range;
            }
            const aggregate = reused orelse
                (aggregateAround(tags, last_tok, t) orelse return false);
            enclosing = aggregate;
            if (!try self.aggregateHasContext(
                context_info,
                aggregate.first,
                aggregate.last,
            )) return false;
        }
        return references != 0;
    }

    fn aggregateHasContext(
        self: *const ArenaProof,
        context_info: *const file_model.TypeInfo,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ProofError!bool {
        const tags = self.tree.tokens.items(.tag);
        var t = first + 1;
        while (t + 3 < last) : (t += 1) {
            if (tags[t] != .period or tags[t + 1] != .identifier or
                !std.mem.eql(u8, self.tree.tokenSlice(t + 1), "ctx") or
                tags[t + 2] != .equal)
                continue;
            var value = t + 3;
            if (value + 2 >= last) continue;
            if (tags[value] == .builtin and
                std.mem.eql(u8, self.tree.tokenSlice(value), "@ptrCast") and
                tags[value + 1] == .l_paren)
                value += 2;
            if (tags[value] != .ampersand) continue;
            const path = pathForward(self.tree, value + 1, last) orelse continue;
            const resolver = self.cache.zls orelse return false;
            const owner_fn = (try resolver.enclosingFunctionAt(t)) orelse continue;
            const owner = self.pathFinalType(owner_fn, &path) orelse continue;
            if (owner == context_info) return true;
        }
        return false;
    }

    fn findGlobalDecl(self: *const ArenaProof, name: []const u8) ?Ast.full.VarDecl {
        const tags = self.tree.tokens.items(.tag);
        for (self.tree.rootDecls()) |node| {
            const decl = self.tree.fullVarDecl(node) orelse continue;
            const name_token = decl.ast.mut_token + 1;
            if (name_token < tags.len and tags[name_token] == .identifier and
                std.mem.eql(u8, self.tree.tokenSlice(name_token), name))
                return decl;
        }
        return null;
    }
};

fn listUsesArenaBackedAllocator(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    index: *DeclIndex,
    fn_decl: ?Ast.Node.Index,
    return_tok: Ast.TokenIndex,
    list_name: []const u8,
) ProofError!bool {
    const decl = fn_decl orelse return false;
    const model = try cache.fileModel();
    const proof = ArenaProof{ .tree = tree, .model = model, .cache = cache, .index = index };
    return proof.listUsesArena(decl, return_tok, list_name);
}

/// True when `return recv.items;` hands the caller a view of a header a
/// container still owns: `if (self.memo.get(key)) |cached| return
/// cached.items;`.  `cached` is not an owner but a second name for an
/// entry the caller keeps, so nothing is lost when it dies at the
/// `return` — and the proof also has to hold for everything behind it.
/// Grow the copy and it owns a buffer nobody else can reach; free it and
/// the returned slice is dangling; hand it to a callee and nothing in
/// this file says what comes back.  Every one of those refuses the site
/// instead of granting it.
fn returnsBorrowedContainerValue(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    index: *DeclIndex,
    fn_decl: ?Ast.Node.Index,
    return_tok: Ast.TokenIndex,
    recv: []const u8,
) !bool {
    const decl = fn_decl orelse return false;
    const model = try cache.fileModel();
    const borrow = ContainerBorrow{
        .tree = tree,
        .model = model,
        .cache = cache,
        .index = index,
    };
    return try borrow.borrowedView(decl, return_tok, recv);
}

/// What the callee of one call does to storage, read from the callee's own
/// body and from nothing else.  `rooted` is charged to the formals the call
/// wrote, so the caller's own storage decides it; `unrooted` is storage the
/// callee reached on its own, which no argument of the call can place.
const CalleeRelease = enum { none, rooted, unrooted, unreadable };

const ContainerBorrow = struct {
    tree: *const Ast,
    model: *const file_model.FileModel,
    cache: *file_cache_mod.FileCache,
    index: *DeclIndex,

    const Capture = struct {
        container: ProofPath,
        container_node: Ast.Node.Index,
        lookup_node: Ast.Node.Index,
        branch_first: Ast.TokenIndex,
        branch_last: Ast.TokenIndex,
    };

    /// The arena proof's receiver resolution over these same fields, so
    /// a map reached through `self` is read exactly the way that proof
    /// reads `self.arena` rather than through a second, looser walk.
    fn receiverRootType(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
    ) ?*const file_model.TypeInfo {
        const proof = ArenaProof{
            .tree = self.tree,
            .model = self.model,
            .cache = self.cache,
            .index = self.index,
        };
        return proof.pathRootType(fn_decl, path);
    }

    fn borrowedView(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        return_tok: Ast.TokenIndex,
        recv: []const u8,
    ) !bool {
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        const bindings = try self.cache.localBindings(proto, body);
        for (bindings.items) |_| try self.index.spend(return_tok);
        const binding = bindings.findAt(recv, return_tok) orelse return false;
        if (binding.origin != .loop_capture) return false;
        const capture = try self.findCapture(fn_decl, return_tok, recv, binding.name_token) orelse return false;
        if (!try self.containerStoresLists(fn_decl, &capture)) return false;
        return try self.branchLeavesThemAlone(fn_decl, &capture, recv);
    }

    /// The innermost `if`/`while` payload that binds `recv` around the
    /// `return` and reaches it through a non-owning `get` on a
    /// container.  A `for` payload is deliberately not one: it binds an
    /// element of a sequence rather than the unwrapped value of a
    /// lookup, and what keeps that element alive is the sequence's
    /// producer, which is a different proof than this one makes.
    fn findCapture(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        return_tok: Ast.TokenIndex,
        recv: []const u8,
        name_token: Ast.TokenIndex,
    ) !?Capture {
        const fn_first = self.tree.firstToken(fn_decl);
        const fn_last = self.tree.lastToken(fn_decl);
        var best: ?Capture = null;
        var scan = try self.index.scanNodes(fn_decl, fn_first, fn_last);
        while (try scan.next()) |node| {
            const tag = self.tree.nodeTag(node);
            if (tag != .@"if" and tag != .if_simple and tag != .@"while" and
                tag != .while_simple and tag != .while_cont) continue;
            var payload: ?Ast.TokenIndex = null;
            var cond_expr: Ast.Node.Index = undefined;
            var branch: Ast.Node.Index = undefined;
            switch (tag) {
                .@"if", .if_simple => {
                    const info = self.tree.fullIf(node) orelse continue;
                    payload = info.payload_token;
                    cond_expr = info.ast.cond_expr;
                    branch = info.ast.then_expr;
                },
                else => {
                    const info = self.tree.fullWhile(node) orelse continue;
                    payload = info.payload_token;
                    cond_expr = info.ast.cond_expr;
                    branch = info.ast.then_expr;
                },
            }
            const payload_token = payload orelse continue;
            if (payload_token != name_token) continue;
            if (!tokenIsNamed(self.tree, payload_token, recv)) continue;
            const branch_first = self.tree.firstToken(branch);
            const branch_last = self.tree.lastToken(branch);
            if (return_tok < branch_first or return_tok > branch_last) continue;
            if (best != null and branch_first <= best.?.branch_first) continue;

            // The payload unwraps the condition, so the only value that
            // can be behind it is what the condition evaluated.  `get`
            // leaves the entry stored in the map; every accessor that
            // hands the value over instead (`pop`, `fetchRemove`) stops
            // here with the caller holding the only header.
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&call_buf, cond_expr) orelse continue;
            const callee = fieldCallee(self.tree, call.ast.fn_expr) orelse continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(callee.method), "get")) continue;
            const container = pathEndingAt(
                self.tree,
                self.tree.lastToken(callee.receiver),
            ) orelse continue;
            best = .{
                .container = container,
                .container_node = callee.receiver,
                .lookup_node = cond_expr,
                .branch_first = branch_first,
                .branch_last = branch_last,
            };
        }
        return best;
    }

    /// The container must be a standard map of the standard list
    /// reached through this method's own pointer receiver.  That is what
    /// makes `get` a copy of a header the caller keeps, and it is why
    /// the owner outlives the call: the receiver does.  A map local to
    /// the function, a container behind a parameter, an alias, a project
    /// type with its own `get` — none of those is proven, so they
    /// report.
    fn containerStoresLists(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        capture: *const Capture,
    ) !bool {
        const container = &capture.container;
        if (container.len == 0) return false;
        const root = self.receiverRootType(fn_decl, container) orelse return false;
        const leaf = walkFieldChain(self.tree, self.model, root, container) orelse return false;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        var params = proto.iterate(self.tree);
        const receiver = params.next() orelse return false;
        const receiver_token = receiver.name_token orelse return false;
        const bindings = try self.cache.localBindings(proto, body);
        for (bindings.items) |_| try self.index.spend(receiver_token);
        const root_binding = bindings.findAt(container.root, self.tree.firstToken(capture.container_node)) orelse return false;
        if (root_binding.origin != .param or root_binding.name_token != receiver_token) return false;
        if (self.cache.zls) |resolver| {
            // The actual SDK declaration settles both lookup semantics and
            // instantiated value type. A project method named get is not proof.
            try self.index.spend(self.tree.nodeMainToken(capture.lookup_node));
            const reference = switch (try resolver.functionReferenceOfCall(capture.lookup_node)) {
                .function => |reference| reference,
                else => return false,
            };
            const function = reference.actual_type.data.function;
            if (!std.mem.eql(u8, function.name orelse return false, "get")) return false;
            if (!try sdkMapDocument(resolver, function.handle)) return false;
            try self.index.spend(self.tree.nodeMainToken(capture.container_node));
            const map = (try resolver.containerOfNode(capture.container_node)) orelse return false;
            if (!try sdkMapDocument(resolver, map.scope_handle.handle)) return false;
            try self.index.spend(self.tree.nodeMainToken(capture.lookup_node));
            return try actualStandardList(resolver, self.index, capture.lookup_node);
        }
        return self.mapStoresStandardList(leaf.type_first, leaf.type_last);
    }

    fn sdkMapDocument(
        resolver: *resolver_mod.TypeResolver,
        handle: @import("type_engine").DocumentStore.Handle,
    ) !bool {
        return try resolver.declaredInToolchainFile(handle, "/std/array_hash_map.zig") or
            try resolver.declaredInToolchainFile(handle, "/std/hash_map.zig");
    }

    /// `std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8))`
    /// is the memo shape: a container whose stored values are the
    /// standard list.  Only the standard library's own map names answer,
    /// and only when what they store is that list, because that pair is
    /// what makes `get` a read rather than a handover.
    fn mapStoresStandardList(
        self: *const ContainerBorrow,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) bool {
        const tags = self.tree.tokens.items(.tag);
        // ONE walk settles both the namespace and the name: the argument
        // group is part of the type written, so the walk is asked to step
        // over it and answers with the declaration the group instantiates.
        const found = std_types.declaration(
            self.cache,
            self.tree,
            first,
            last,
            std_type_policy,
        ) orelse return false;
        // `std.hash_map.Name` names the same type as `std.Name`, so the
        // two namespaces are one name read against the names each of
        // them actually declares.
        if (found.module.len != 0 and !std.mem.eql(u8, found.module, "hash_map")) return false;
        if (!isStdMapName(found.module, found.name)) return false;
        var open: Ast.TokenIndex = first;
        while (open < last and tags[open] != .l_paren) : (open += 1) {}
        if (open >= last) return false;
        const close = tokens.matchParen(tags, open, last) orelse return false;
        if (close != last) return false;
        // `StringArrayHashMap` spells its key as a `[]const u8`
        // parameter and takes the value alone; every other map takes
        // the key first.  Which group is the VALUE is a property of the
        // map's own declaration, and it is the only thing that walk
        // cannot say — so it is read here, from the argument group
        // itself, once.
        const value = argumentGroup(
            tags,
            open,
            close,
            if (std.mem.startsWith(u8, found.name, "StringArrayHashMap")) 0 else 1,
        ) orelse return false;
        return isStandardListType(self.cache, self.tree, value.first, value.last);
    }

    /// Between the capture and the `return`, the borrowed header, the
    /// container that owns it and anything that could outlive the branch
    /// are all left exactly as they were found.
    fn branchLeavesThemAlone(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        capture: *const Capture,
        recv: []const u8,
    ) !bool {
        const fn_first = self.tree.firstToken(fn_decl);
        const fn_last = self.tree.lastToken(fn_decl);
        var scan = try self.index.scanNodes(fn_decl, fn_first, fn_last);
        while (try scan.next()) |node| {
            const first = self.tree.firstToken(node);
            const in_branch = first >= capture.branch_first and
                first <= capture.branch_last;
            switch (self.tree.nodeTag(node)) {
                .@"asm", .asm_simple, .asm_input, .asm_output => if (in_branch) return false,
                .fn_decl => {
                    // A function declared in the branch can outlive it,
                    // and the capture it copied would then be the last
                    // name the header has.
                    if (in_branch) return false;
                },
                .address_of => {
                    // `&map` hands the container to a callee that can
                    // write to it behind this walk's back.
                    const operand = self.tree.nodeData(node).node;
                    if (self.reachesContainer(operand, &capture.container)) return false;
                    if (in_branch and self.tree.nodeTag(operand) == .identifier and
                        tokenIsNamed(self.tree, self.tree.nodeMainToken(operand), recv))
                        return false;
                },
                .assign => {
                    if (!in_branch) continue;
                    const lhs = self.tree.nodeData(node).node_and_node[0];
                    if (self.reachesContainer(lhs, &capture.container)) return false;
                    if (self.tree.nodeTag(lhs) != .identifier) continue;
                    if (tokenIsNamed(self.tree, self.tree.nodeMainToken(lhs), recv)) return false;
                },
                .call, .call_comma, .call_one, .call_one_comma => {
                    if (!in_branch) continue;
                    var call_buf: [1]Ast.Node.Index = undefined;
                    // A call whose arguments this walk cannot read is a
                    // call this walk cannot clear.
                    const call = self.tree.fullCall(&call_buf, node) orelse return false;
                    if (!try self.callLeavesTheCaptureAlone(fn_decl, capture, recv, call))
                        return false;
                },
                else => {},
            }
        }
        return true;
    }

    /// One call written between the capture and the `return`.
    ///
    /// The capture dies here, so the only question is whether this call can
    /// take the bytes behind it away first, and it is answered from two
    /// facts rather than from an effect query: what the CALLEE's own body
    /// releases, and whether any value THIS call handed it is the receiver's
    /// own storage.
    ///
    /// The two are asked in that order because they answer different
    /// questions.  A callee that releases nothing cannot take the bytes no
    /// matter what it was handed — `visit(members)` whose body reads a count
    /// out of the map is the same call as `visit(members, gpa)` whose body
    /// frees every entry, and the argument list is not what tells them
    /// apart.  A callee that releases storage it was NOT handed cannot be
    /// discharged by any argument at all: `visit()` with an empty parameter
    /// list still returns the capture to the allocator that issued it,
    /// through a global this file cannot place.  What is left is a callee
    /// that releases what one of its formals names, and the storage is the
    /// caller's only if one of the values this call wrote is the receiver's
    /// own — the container the capture came from, another field of the same
    /// value, or a local this function built out of either.
    fn callLeavesTheCaptureAlone(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        capture: *const Capture,
        recv: []const u8,
        call: Ast.full.Call,
    ) !bool {
        const fn_expr = call.ast.fn_expr;
        // The receiver sits where a method's first formal would, so it is
        // one more value this call handed over and is read as one — the
        // AST says so outright, which is why the argument list does not
        // have to be asked a question to find out whether there was one.
        var reaches_receiver = false;
        if (self.tree.nodeTag(fn_expr) == .field_access) {
            const receiver = self.tree.nodeData(fn_expr).node_and_token[0];
            if (try self.handedOverReaches(fn_decl, capture, recv, receiver))
                reaches_receiver = true;
        }
        for (call.ast.params) |param| {
            if (try self.handedOverReaches(fn_decl, capture, recv, param))
                reaches_receiver = true;
        }
        const callee_token = self.tree.lastToken(fn_expr);
        const actual = try call_summary.actualCallSummaryAt(
            self.cache,
            fresh_storage.calleeQueryToken(self.tree, call),
            null,
        );
        const release: CalleeRelease = if (actual) |summary|
            try self.calleeRelease(summary.callee)
        else if (isReleaseName(self.tree.tokenSlice(callee_token)))
            // A callee this rule cannot resolve to a declaration is read on
            // the name the call is written with, and `other.deinit(…)`
            // releases what `other` is.  It is charged to what the call
            // wrote rather than granted, which is the same refusal a
            // readable body gets for a release it reached on its own.
            CalleeRelease.rooted
        else
            CalleeRelease.unreadable;
        return switch (release) {
            .none => true,
            .unrooted => false,
            .rooted, .unreadable => !reaches_receiver,
        };
    }

    /// One value this call was handed.  The capture itself is refused on
    /// sight — handing the borrowed header to a callee is handing over the
    /// only name it has — and anything else is asked whether its storage is
    /// the receiver's own.
    fn handedOverReaches(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        capture: *const Capture,
        recv: []const u8,
        node: Ast.Node.Index,
    ) !bool {
        try self.index.spend(self.tree.firstToken(node));
        if (self.tree.nodeTag(node) == .identifier and
            tokenIsNamed(self.tree, self.tree.nodeMainToken(node), recv)) return true;
        return self.reachesReceiverStorage(fn_decl, capture, node, 0);
    }

    /// What the callee releases, read from the callee's own body.
    fn calleeRelease(
        self: *const ContainerBorrow,
        callee: file_cache_mod.FileCache.ActualCallee,
    ) !CalleeRelease {
        // A body outside the analysed file is not one this rule reads: the
        // walk below is bounded by this file's tokens, and a standard
        // library body is not in them.  It is charged, never granted.
        if (callee.tree != self.tree) return .unreadable;
        const tree = callee.tree;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buf, callee.declaration) orelse
            return .unreadable;
        const body = tokens.bodyOf(tree, callee.declaration) orelse return .unreadable;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        const tags = tree.tokens.items(.tag);

        var names: std.ArrayListUnmanaged([]const u8) = .empty;
        defer names.deinit(self.index.gpa);
        var params = proto.iterate(tree);
        while (params.next()) |param| {
            const name_token = param.name_token orelse continue;
            try self.index.spend(name_token);
            try names.append(self.index.gpa, tree.tokenSlice(name_token));
        }
        // A payload bound from an iterable that names a formal reaches that
        // formal's storage: `for (members.values()) |*entry| gpa.free(
        // entry.…)` releases what `members` owns, even though the name the
        // release is written on is the body's own.
        var t = first;
        while (t < last) : (t += 1) {
            if (tags[t] != .keyword_for) continue;
            var open = t + 1;
            while (open < last and tags[open] != .l_paren) : (open += 1) {}
            if (open >= last) continue;
            const close = tokens.matchParen(tags, open, last) orelse continue;
            if (!mentionsAny(tree, open + 1, close -| 1, names.items)) continue;
            var bar = close + 1;
            while (bar < last and tags[bar] != .pipe) : (bar += 1) {}
            if (bar >= last) continue;
            var end = bar + 1;
            while (end < last and tags[end] != .pipe) : (end += 1) {}
            var p = bar + 1;
            while (p < end) : (p += 1) {
                if (tags[p] != .identifier) continue;
                try self.index.spend(p);
                try names.append(self.index.gpa, tree.tokenSlice(p));
            }
        }

        var verdict: CalleeRelease = .none;
        t = first;
        while (t + 1 <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!isReleaseName(tree.tokenSlice(t))) continue;
            // `name (…` is a free function and `recv . name (…` a method,
            // and the receiver is as much a source of what is released as
            // the argument beside it.
            const expr_first = if (t >= 2 and tags[t - 1] == .period and
                tags[t - 2] == .identifier) t - 2 else t;
            const open = if (tags[t + 1] == .l_paren) t + 1 else continue;
            const close = tokens.matchParen(tags, open, last) orelse continue;
            try self.index.spend(t);
            const rooted = mentionsAny(tree, expr_first, close, names.items);
            if (!rooted) verdict = .unrooted;
            if (rooted and verdict == .none) verdict = .rooted;
        }
        return verdict;
    }

    /// True when the storage this expression names is the receiver's own:
    /// the container the capture was read out of, another field of the same
    /// value, or a local this function built out of either.  A value from
    /// anywhere else — a local built from a resolved constructor, a standard
    /// library singleton — is not, and a question this walk cannot finish is
    /// charged rather than granted.
    fn reachesReceiverStorage(
        self: *const ContainerBorrow,
        fn_decl: Ast.Node.Index,
        capture: *const Capture,
        node: Ast.Node.Index,
        depth: u8,
    ) !bool {
        try self.index.spend(self.tree.firstToken(node));
        const first = self.tree.firstToken(node);
        const last = self.tree.lastToken(node);
        const tags = self.tree.tokens.items(.tag);
        var t = first;
        while (t <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            const name = self.tree.tokenSlice(t);
            if (std.mem.eql(u8, name, capture.container.root)) return true;
            const decl = (try self.index.lookup(fn_decl, name, t)) orelse continue;
            const init = decl.init_node.unwrap() orelse continue;
            if (depth + 1 >= receiver_depth_limit) return self.index.tooDeep(t, receiver_depth_limit);
            if (try self.reachesReceiverStorage(fn_decl, capture, init, depth + 1))
                return true;
        }
        return false;
    }

    /// True when `node` names the container itself, or anything reached
    /// through it.
    fn reachesContainer(
        self: *const ContainerBorrow,
        node: Ast.Node.Index,
        container: *const ProofPath,
    ) bool {
        const path = pathEndingAt(self.tree, self.tree.lastToken(node)) orelse return false;
        return path.startsWith(container);
    }
};

/// True when any of `names` is spelled between `first` and `last`.
fn mentionsAny(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    names: []const []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t <= last and t < tags.len) : (t += 1) {
        if (tags[t] != .identifier) continue;
        for (names) |name| {
            if (std.mem.eql(u8, tree.tokenSlice(t), name)) return true;
        }
    }
    return false;
}

/// Entry points that hand storage back to whoever issued it, or take it
/// away for good.  This is the name-evidence surface the borrowed-container
/// proof reads a callee's body through, and it is deliberately the same
/// surface the file-wide evidence scan in `ref-counted-copy-without-dupe`
/// uses: a body that spells none of these releases nothing this rule can
/// see, and a body that spells one is read on the value it was written on.
fn isReleaseName(name: []const u8) bool {
    const names = [_][]const u8{
        "clearAndFree",   "destroy",       "deinit",               "fetchRemove",
        "fetchRemoveGet", "free",          "rawFree",              "release",
        "remove",         "shrinkAndFree", "shrinkAndFreePrecise", "unref",
    };
    for (names) |candidate| {
        if (std.mem.eql(u8, name, candidate)) return true;
    }
    return false;
}

/// Entry points of the standard list that take an allocator and can move,
/// resize or rebind its backing buffer.  Every one of them is charged: the
/// arena proof claimed a list stayed arena-backed while a caller-supplied
/// allocator reached `ensureTotalCapacity`, `addOne`, `print` or any of the
/// rest and reallocated what an arena had already grown.
///
/// The surface is the UNMANAGED half of `std/array_list.zig`, and that is
/// not a choice of spelling: `std.ArrayList(T)` has been
/// `array_list.Aligned(T, null)` since 0.16, and `Aligned` is the only name
/// inside that file read as this list.  `array_list.Managed` /
/// `AlignedManaged` hold their allocator in the header, so their `append`
/// carries the ITEM where this one carries the allocator — a different
/// type, a different proof, and `localIsStandardList` refuses it rather
/// than reading it through these names.
///
/// Every entry below is therefore a real `Aligned` declaration whose
/// allocator is `gpa: Allocator` as the first parameter after `self`
/// (array_list.zig: addManyAt 754, addOne 1262, addManyAsArray 1298,
/// addManyAsSlice 1339, append 903, appendNTimes 1071, appendSlice 983,
/// appendUnalignedSlice 1011, ensureTotalCapacity 1209,
/// ensureTotalCapacityPrecise 1217, ensureUnusedCapacity 1245, insert 709,
/// insertSlice 807, print 1042, replaceRange 853, resize 1111) — which is
/// exactly why `chargeGrowth` reads the first written argument.
///
/// The `*AssumeCapacity` and `*Bounded` forms are absent because they take
/// no allocator at all and cannot reallocate: each returns
/// `error.OutOfMemory` or writes into capacity already reserved
/// (appendBounded 923, addOneBounded 1290, printBounded 1059, and their
/// twins).  Charging one read its FIRST argument — the item, not an
/// allocator — as the buffer's owner and refused sites the rule's own
/// contract discharges.  `clone` (698), `fromOwnedSlice` (636) and
/// `toManaged` (630) are absent for the opposite reason: they take an
/// allocator without ever moving THIS list's buffer.
fn listGrowthMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "addManyAsArray") or
        std.mem.eql(u8, name, "addManyAsSlice") or
        std.mem.eql(u8, name, "addManyAt") or
        std.mem.eql(u8, name, "addOne") or
        std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendNTimes") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "appendUnalignedSlice") or
        std.mem.eql(u8, name, "ensureTotalCapacity") or
        std.mem.eql(u8, name, "ensureTotalCapacityPrecise") or
        std.mem.eql(u8, name, "ensureUnusedCapacity") or
        std.mem.eql(u8, name, "insert") or
        std.mem.eql(u8, name, "insertSlice") or
        std.mem.eql(u8, name, "print") or
        std.mem.eql(u8, name, "replaceRange") or
        std.mem.eql(u8, name, "resize");
}

/// Entry points that free the block `.items` names, or hand it to the
/// caller.  Whoever allocated it stops mattering: a `deinit` — even one
/// reached through `defer`, and even through the same arena — leaves the
/// returned slice pointing at released memory, so the arena proof cannot
/// stand.  The two `…Assert` forms free nothing, but they hand the whole
/// block back while the header stays behind, which loses it the same way.
fn listReleasesBuffer(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "clearAndFree") or
        std.mem.eql(u8, name, "shrinkAndFree") or
        std.mem.eql(u8, name, "shrinkAndFreePrecise") or
        std.mem.eql(u8, name, "shrinkToLen") or
        std.mem.eql(u8, name, "shrinkToLenSentinel") or
        std.mem.eql(u8, name, "toOwnedSlice") or
        std.mem.eql(u8, name, "toOwnedSliceSentinel") or
        std.mem.eql(u8, name, "toOwnedSliceAssert") or
        std.mem.eql(u8, name, "toOwnedSliceSentinelAssert");
}

/// The standard list's constructors.  Their receiver is the type rather than
/// the local, so the walk reads them on the declaration they initialise.
/// `Aligned` has exactly one allocator-taking constructor — `initCapacity`
/// (array_list.zig:604); `init` and `fromOwnedSlice` are the managed
/// half's, and `initBuffer` takes a buffer rather than an allocator.
fn isListConstructor(name: []const u8) bool {
    return std.mem.eql(u8, name, "initCapacity");
}

/// Constructors that bind the list to a buffer SOMEONE ELSE already owns:
/// `initBuffer(&buf)` names a stack or static array outright, and
/// `fromOwnedSlice` / `fromOwnedSliceSentinel` take over a slice whose
/// provenance this file never proves.  None of them takes an allocator,
/// so charging one would read their first argument — the buffer, or a
/// length — as the buffer's owner; and the owner they bind is not an
/// arena this proof can see, so the site is refused rather than charged.
/// An ANNOTATED declaration is what makes this reachable: with no
/// annotation the walk reads the initializer for the type name instead
/// and never gets here.
fn listTakesForeignBuffer(name: []const u8) bool {
    return std.mem.eql(u8, name, "initBuffer") or
        std.mem.eql(u8, name, "fromOwnedSlice") or
        std.mem.eql(u8, name, "fromOwnedSliceSentinel");
}

fn unwrapTry(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    return if (tree.nodeTag(node) == .@"try") tree.nodeData(node).node else node;
}

/// `a.b.c` read forward from `first`.  The terminator test keeps a partial
/// path (`self.ar`) from reading as if it named a longer chain.
fn pathForward(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) ?ProofPath {
    const tags = tree.tokens.items(.tag);
    if (first > last or first >= tags.len or tags[first] != .identifier) return null;
    var path: ProofPath = .{ .root = tree.tokenSlice(first) };
    var t = first;
    while (t + 2 <= last and tags[t + 1] == .period and
        tags[t + 2] == .identifier)
    {
        if (!path.push(tree.tokenSlice(t + 2))) return null;
        t += 2;
    }
    if (t + 1 > last) return null;
    return switch (tags[t + 1]) {
        .r_paren, .comma, .r_brace => path,
        else => null,
    };
}

/// The same path read backward from the identifier at `last`, for a caller
/// that holds a field's last token and needs the receiver chain it belongs
/// to.  `root` is the leftmost name; `segments` is the chain in source
/// order, so both constructors hand the rest of the proof one shape.
fn pathEndingAt(tree: *const Ast, last: Ast.TokenIndex) ?ProofPath {
    const tags = tree.tokens.items(.tag);
    if (last >= tags.len or tags[last] != .identifier) return null;
    var path: ProofPath = .{ .root = undefined };
    var t = last;
    while (t >= 2 and tags[t - 1] == .period and tags[t - 2] == .identifier) {
        if (!path.push(tree.tokenSlice(t))) return null;
        t -= 2;
    }
    // The walk ends on the LEFTMOST name of the chain, and that is what
    // `root` means: `pathRootType` compares it against the receiver's own
    // name, so reading `self.completion_ctx` as root `completion_ctx` would
    // fail to resolve `self` and lose the whole chain.
    path.root = tree.tokenSlice(t);
    // Filled right-to-left above; the proof walks it left-to-right.
    var i: usize = 0;
    while (i + 1 < path.len) : (i += 1) {
        std.mem.swap([]const u8, &path.segments[i], &path.segments[path.len - 1 - i]);
    }
    return path;
}

fn baseTypeName(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t < last and (tags[t] == .asterisk or tags[t] == .keyword_const or
        tags[t] == .question_mark)) : (t += 1)
    {}
    return if (t == last and tags[t] == .identifier) tree.tokenSlice(t) else null;
}

/// The field a receiver chain ends at: `self.context.alloc` resolves to the
/// `alloc` field of whatever `context`'s own type declares, and the caller
/// reads the leaf it is about — its declared type tokens for an
/// `isArenaType` / `mapStoresStandardList` proof, or the type it names for a
/// `pathFinalType` proof.  Every chain in this file is walked the same way,
/// so the walk is written once here.
///
/// Null is a chain that does not resolve — a field this file does not
/// declare, or an intermediate type that is not one of its own — and no
/// caller reads anything else out of a null.  A chain of no segments names
/// no field and answers null as well; the callers that can accept the root
/// type itself handle that case before asking.
fn walkFieldChain(
    tree: *const Ast,
    model: *const file_model.FileModel,
    root: *const file_model.TypeInfo,
    path: *const ProofPath,
) ?*const file_model.FieldInfo {
    var type_info = root;
    var i: usize = 0;
    while (i < path.len) : (i += 1) {
        const field = type_info.findField(path.segments[i]) orelse return null;
        if (i + 1 == path.len) return field;
        const name = baseTypeName(tree, field.type_first, field.type_last) orelse
            return null;
        type_info = model.findType(name) orelse return null;
    }
    return null;
}

/// The policy every identity read in this file asks with.  A generic
/// argument group is part of the expression it is written in —
/// `std.ArrayList(u8)` says WHICH list it is — and a pointer, `const`,
/// `volatile` or optional in front of the name qualifies that same name
/// rather than replacing it.  Nothing else is stepped over to reach the
/// name, so the walk reads a declaration or answers that it read none.
const std_type_policy: std_types.Policy = .{
    .allow_type_call = true,
    .allow_pointer = true,
};

/// The standard library's own TOP-LEVEL growable-list names: what
/// `std.zig` declares beside `ArrayList`, which is that function plus the
/// three spellings that alias it (`std.zig`:47,55,57,59).  `Aligned` is
/// deliberately not among them — it is declared inside
/// `std/array_list.zig`, not beside `ArrayList` — so a top-level
/// `std.Aligned` names no declaration this rule can discharge, however
/// much it reads like one.
fn isStdTopLevelListName(name: []const u8) bool {
    return std.mem.eql(u8, name, "ArrayList") or
        std.mem.eql(u8, name, "ArrayListUnmanaged") or
        std.mem.eql(u8, name, "ArrayListAligned") or
        std.mem.eql(u8, name, "ArrayListAlignedUnmanaged");
}

/// The names inside `std/array_list.zig` this rule discharges, which is
/// the UNMANAGED half only.  `Aligned` (array_list.zig:570) carries its
/// allocator in each growth call, which is exactly the argument
/// `chargeGrowth` reads.  `Managed` (11) and `AlignedManaged` (16) hold
/// theirs in the header instead, so their `append` carries the ITEM
/// where this one's carries the allocator — a different type and a
/// different proof, so they are refused here rather than read through
/// the unmanaged names.
fn isStdArrayListName(name: []const u8) bool {
    return std.mem.eql(u8, name, "Aligned");
}

/// True when `[first, last]` spells the standard library's growable
/// list: `std.ArrayList(T)`, `std.ArrayListUnmanaged(T)`,
/// `std.ArrayListAligned(T, alignment)`,
/// `std.ArrayListAlignedUnmanaged(T, alignment)` and
/// `std.array_list.Aligned(T, alignment)` are one type, and so is a
/// `const` alias of one — at file scope or inside the body that uses it.
///
/// ONE `declaration` walk answers it, and the answer is then compared
/// against the names above.  That walk is what proves `std` is the
/// import and what follows an alias; this file reads no source text of
/// its own to decide which names the library has.  Asking `isType` per
/// candidate name instead would spend one resolution walk on every name
/// that does NOT match, so a rejected spelling would cost more than an
/// accepted one — five to twelve walks where one settles the whole list.
fn isStandardListType(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const found = std_types.declaration(cache, tree, first, last, std_type_policy) orelse
        return false;
    if (found.module.len == 0) return isStdTopLevelListName(found.name);
    return std.mem.eql(u8, found.module, "array_list") and
        isStdArrayListName(found.name);
}

/// The standard library's map types.  `get` on one of these reads a
/// stored value; nothing else in the standard library hands a stored
/// header back as a value while leaving it stored.
///
/// Each namespace is compared against the names IT declares, which is
/// why this takes the namespace and not a name alone.  `std.zig` exports
/// six `hash_map` names directly (std.zig:1,17,28,29) and three
/// `array_hash_map` ones (37,39,41); the managed `StringArrayHashMap` /
/// `ArrayHashMap` / `AutoArrayHashMap` it once exported are declared
/// nowhere in this toolchain, so a file spelling one is not writing a
/// standard map.  `std.hash_map` declares only its own six
/// (hash_map.zig:46,50,64,70,135,505) and none of the array maps.
fn isStdMapName(module: []const u8, name: []const u8) bool {
    if (std.mem.eql(u8, name, "HashMap") or
        std.mem.eql(u8, name, "HashMapUnmanaged") or
        std.mem.eql(u8, name, "StringHashMap") or
        std.mem.eql(u8, name, "StringHashMapUnmanaged") or
        std.mem.eql(u8, name, "AutoHashMap") or
        std.mem.eql(u8, name, "AutoHashMapUnmanaged")) return true;
    if (module.len != 0) return false;
    return std.mem.eql(u8, name, "StringArrayHashMapUnmanaged") or
        std.mem.eql(u8, name, "ArrayHashMapUnmanaged") or
        std.mem.eql(u8, name, "AutoArrayHashMapUnmanaged");
}

/// `std.ArrayList(u8){ .items = &.{} }` — a header written from literals
/// owns no allocation, but only once its own type is the standard list.
fn isStandardListLiteral(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    node: Ast.Node.Index,
) bool {
    const tags = tree.tokens.items(.tag);
    const last = tree.lastToken(node);
    var t = tree.firstToken(node);
    while (t < last and tags[t] != .l_brace) : (t += 1) {}
    if (t == last) return false;
    return isStandardListType(cache, tree, tree.firstToken(node), t - 1);
}

/// The `index`th comma-separated argument of the call group
/// `[open, close]`, counted from zero.  Only commas at the group's own
/// depth separate arguments, so a nested generic group stays whole.
fn argumentGroup(
    tags: []const std.zig.Token.Tag,
    open: Ast.TokenIndex,
    close: Ast.TokenIndex,
    index: usize,
) ?AggregateRange {
    var depth: u32 = 0;
    var seen: usize = 0;
    var start = open + 1;
    var t = open + 1;
    while (t < close) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => depth -|= 1,
            .comma => if (depth == 0) {
                if (seen == index) return .{ .first = start, .last = t - 1 };
                seen += 1;
                start = t + 1;
            },
            else => {},
        }
    }
    return if (seen == index and start < close)
        .{ .first = start, .last = close - 1 }
    else
        null;
}

/// True when `token` is an identifier reading `name`.
fn tokenIsNamed(tree: *const Ast, token: Ast.TokenIndex, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    return token < tags.len and tags[token] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(token), name);
}

/// The two parts of a method call written `receiver . method(…)`: the
/// node the receiver chain is rooted at, and the token the method NAME
/// is written at.  Null when the callee is spelled any other way.
///
/// Every walk below that asks "which method is this call" reads exactly
/// this pair — the arena proof for a growth or release entry point, the
/// constructor check on a declaration and on a rebinding, and the
/// borrowed-container proof for its `get` — so the shape of a field
/// access is settled once instead of at each of those sites.
fn fieldCallee(tree: *const Ast, fn_expr: Ast.Node.Index) ?struct {
    receiver: Ast.Node.Index,
    method: Ast.TokenIndex,
} {
    if (tree.nodeTag(fn_expr) != .field_access) return null;
    const access = tree.nodeData(fn_expr).node_and_token;
    return .{ .receiver = access[0], .method = access[1] };
}

/// The policy the two NAMED types below are asked with.  Pointer and
/// optional qualifiers are allowed because the receiver this rule has to
/// recognise is written as a pointer more often than not:
/// `*std.heap.ArenaAllocator` is the parameter type whose own node is
/// the proof that the argument came from a real arena, and reading that
/// as `ArenaAllocator` would be reading a different type.  Neither
/// declaration takes an argument group, so none is asked about.
const named_type_policy: std_types.Policy = .{ .allow_pointer = true };

/// `[first, last]` names `std.heap.ArenaAllocator`, and this file proves
/// `std` is the import before the name is compared.  A file-scope or
/// block-scope `const` alias of it answers too — the walk follows the
/// alias itself — while a project type that merely reuses the name, a
/// `var` of that name, or a parameter shadowing it does not.
fn isArenaType(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    return std_types.isType(
        cache,
        tree,
        first,
        last,
        "heap",
        "ArenaAllocator",
        named_type_policy,
    );
}

/// `[first, last]` names `std.mem.Allocator`, read the same way.
fn isAllocatorType(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    return std_types.isType(
        cache,
        tree,
        first,
        last,
        "mem",
        "Allocator",
        named_type_policy,
    );
}

fn aggregateFieldEnd(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    close: Ast.TokenIndex,
) Ast.TokenIndex {
    var depth: u32 = 0;
    var t = first;
    while (t < close) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => depth -|= 1,
            .comma => if (depth == 0) return t,
            else => {},
        }
    }
    return close;
}

/// Innermost `{ … }` enclosing `token`, or null when `token` sits in no
/// block at all.  `last` is the tree's final token index, so the brace
/// walk is bounded by the stream itself rather than a narrowed
/// `tags.len`.
///
/// One backward count of the unbalanced braces finds the innermost open,
/// and only that one is matched forward.  Matching every `{` before the
/// token instead re-read the whole prefix once per brace, so the answer
/// cost the token stream squared even for a single reference.
fn aggregateAround(
    tags: []const std.zig.Token.Tag,
    last: Ast.TokenIndex,
    token: Ast.TokenIndex,
) ?AggregateRange {
    var closed: usize = 0;
    var t = token;
    while (t > 0) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => closed += 1,
            .l_brace => {
                if (closed != 0) {
                    closed -= 1;
                    continue;
                }
                const close = tokens.matchBrace(tags, t, last) orelse return null;
                return if (close >= token) .{ .first = t, .last = close } else null;
            },
            else => {},
        }
    }
    return null;
}

/// True iff `recv` is a pointer-typed parameter of `fn_decl`.
fn recvIsPointerParam(tree: *const Ast, fn_decl: Ast.Node.Index, recv: []const u8) bool {
    // Keep only the proto NODE — `fullFnProto` stores params in a local
    // buf that must outlive the iteration, so resolve the proto here,
    // not in a helper that returns it.
    const proto_node = tree.nodeData(fn_decl).node_and_node[0];
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buf, proto_node) orelse return false;
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        const nt = p.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), recv)) continue;
        const te = p.type_expr orelse return false;
        return switch (tree.nodeTag(te)) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => true,
            else => false,
        };
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    return_tok: Ast.TokenIndex,
) !void {
    const recv = tree.tokenSlice(return_tok + 1);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`return {s}.items` — the caller receives a slice but cannot free the ArrayList's backing allocation; use `return {s}.toOwnedSlice()` to transfer ownership of exactly the used bytes, or document that this is an intentional borrow",
        .{ recv, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, return_tok),
        .end = try Pos.fromTokenEnd(tree, return_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "return-arraylist-items: fires" {
    try testing.expectFires(check, R,
        \\fn convert(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, input.len);
        \\    try list.appendSlice(input);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: toOwnedSlice does not fire" {
    try testing.expectNoFire(check,
        \\fn convert(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, input.len);
        \\    try list.appendSlice(input);
        \\    return list.toOwnedSlice();
        \\}
        \\
    );
}

test "return-arraylist-items: self.items does not fire" {
    try testing.expectNoFire(check,
        \\const Buf = struct { items: []u8 };
        \\fn getItems(self: *Buf) []u8 {
        \\    return self.items;
        \\}
        \\
    );
}

test "return-arraylist-items: this.items does not fire" {
    try testing.expectNoFire(check,
        \\const Buf = struct { items: []u8 };
        \\fn getItems(this: *Buf) []u8 {
        \\    return this.items;
        \\}
        \\
    );
}

test "return-arraylist-items: full-capacity assert suppresses" {
    try testing.expectNoFire(check,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var array = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try fill(&array);
        \\    assert(array.items.len == array.capacity);
        \\    return array.items;
        \\}
        \\
    );
}

test "return-arraylist-items: no capacity check still fires" {
    try testing.expectFires(check, R,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try list.appendSlice(data);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: a capacity read is not a full-capacity proof" {
    // The capacity is read here — to decide whether the append is worth
    // making — and the returned slice still covers less than the whole
    // allocation, so the caller still cannot free it as it stands.  The
    // suppression is for the comparison that says the buffer IS full, not
    // for the mention of the field that comparison would use.
    try testing.expectFires(check, R,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    if (list.capacity > 4) {
        \\        try list.appendSlice(data);
        \\    }
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: the full-capacity comparison reads either way round" {
    try testing.expectNoFire(check,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var array = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try fill(&array);
        \\    assert(array.capacity == array.items.len);
        \\    return array.items;
        \\}
        \\
    );
}

test "return-arraylist-items: a full-capacity comparison across two lists proves nothing" {
    // The reverse orientation reads `recv . capacity` three tokens back from
    // the operator, not five.  That offset is only ever allowed to name THIS
    // list: `other.capacity == list.items.len` is true whenever the two lists
    // happen to agree, and it says nothing about how much of `list`'s own
    // allocation the returned slice covers.
    try testing.expectFires(check, R,
        \\fn build(allocator: Allocator, other: *std.ArrayList(u8)) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try list.appendSlice(data);
        \\    assert(other.capacity == list.items.len);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: pointer param (caller-owned) suppresses" {
    try testing.expectNoFire(check,
        \\fn collect(out: *std.ArrayList(u8)) []u8 {
        \\    out.append(1) catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: by-value param still fires (post-append realloc leaks)" {
    try testing.expectFires(check, R,
        \\fn collect(list: std.ArrayList(u8)) []u8 {
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: declared receiver arena owns returned backing storage" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context) []const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "skript regression: caller allocator output still needs ownership transfer" {
    try testing.expectFires(check, R,
        \\fn render(allocator: std.mem.Allocator) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(allocator, 'x') catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: private call chain preserves declared arena origin" {
    // Every fixture from here on that exercises the PRIVATE-HELPER arm
    // runs on the typed harness, and that is the consumer contract rather
    // than a convenience: the caller set is read by resolving each
    // reference to the declaration it names, so an analysis that cannot
    // resolve declarations cannot settle the question and the site is
    // reported.  A fixture that wanted to assert the quiet case had to
    // earn it from a real type engine, not from the rule's own reading of
    // a name.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Allocator = std.mem.Allocator;
        \\fn own(memory: Allocator, raw: []const u8) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.appendSlice(memory, raw) catch {};
        \\    return out.items;
        \\}
        \\fn hang(memory: Allocator, raw: []const u8) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.appendSlice(memory, raw) catch {};
        \\    return out.items;
        \\}
        \\const Capture = struct {
        \\    fn end(self: *Capture, memory: Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Query = struct {
        \\    text: []const u8,
        \\    fn submit(memory: Allocator) Query {
        \\        var capture: Capture = .{};
        \\        return .{ .text = hang(memory, own(memory, capture.end(memory))) };
        \\    }
        \\};
        \\fn add(_: Query) void {}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn evaluate(self: *Model) void {
        \\        add(.submit(self.arena.allocator()));
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: unrelated function pointer parameter cannot reach private arena helper" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn collect(memory: std.mem.Allocator) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 'x') catch {};
        \\    return out.items;
        \\}
        \\pub const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Model) []const u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\pub fn unrelated(callback: *const fn () void) void {
        \\    callback();
        \\}
    );
}

test "return-arraylist-items: function pointer parameter can reach escaped private helper" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn collect(memory: std.mem.Allocator) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 'x') catch {};
        \\    return out.items;
        \\}
        \\pub const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Model) []const u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\fn invoke(callback: *const fn (std.mem.Allocator) []const u8, memory: std.mem.Allocator) []const u8 {
        \\    return callback(memory);
        \\}
        \\pub fn heap(memory: std.mem.Allocator) []const u8 {
        \\    return invoke(collect, memory);
        \\}
    );
}

test "return-arraylist-items: unrelated callback does not hide a direct heap caller" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn collect(memory: std.mem.Allocator) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 'x') catch {};
        \\    return out.items;
        \\}
        \\pub const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Model) []const u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\pub fn heap(memory: std.mem.Allocator) []const u8 {
        \\    return collect(memory);
        \\}
        \\pub fn unrelated(callback: *const fn () void) void {
        \\    callback();
        \\}
    );
}

test "return-arraylist-items: bound and unbound private calls preserve the same arena formal" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn collect(self: *Capture, memory: std.mem.Allocator) []u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory, 1) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn evaluate(self: *Model) void {
        \\        var capture: Capture = .{};
        \\        _ = capture.collect(self.arena.allocator());
        \\        _ = Capture.collect(&capture, self.arena.allocator());
        \\    }
        \\};
    );
}

test "return-arraylist-items: arena arguments do not prove a different heap formal" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn collect(self: *Capture, memory: std.mem.Allocator, unused: std.mem.Allocator) []u8 {
        \\        _ = self;
        \\        _ = unused;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory, 1) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn evaluate(self: *Model, heap: std.mem.Allocator) void {
        \\        var capture: Capture = .{};
        \\        _ = capture.collect(heap, self.arena.allocator());
        \\        _ = Capture.collect(&capture, heap, self.arena.allocator());
        \\    }
        \\};
    );
}

test "return-arraylist-items: integer fields do not escape a same-named arena method" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn end(self: *Capture, allocator: std.mem.Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(allocator, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Model) []const u8 {
        \\        var capture: Capture = .{};
        \\        return capture.end(self.arena.allocator());
        \\    }
        \\};
        \\const Range = struct { end: usize };
        \\pub fn length(range: Range) usize {
        \\    const end = range.end;
        \\    return end;
        \\}
    ;
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-arena-method-identity.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "return-arraylist-items: unknown receivers do not select a same-named arena method" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn end(self: *Capture, allocator: std.mem.Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(allocator, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Model, receiver: anytype) []const u8 {
        \\        return receiver.end(self.arena.allocator());
        \\    }
        \\};
    );
}

test "return-arraylist-items: escaped method references still require ownership transfer" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn end(self: *Capture, allocator: std.mem.Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(allocator, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const escaped = Capture.end;
        \\pub fn render(allocator: std.mem.Allocator) []const u8 {
        \\    var capture: Capture = .{};
        \\    return escaped(&capture, allocator);
        \\}
    );
}

test "return-arraylist-items: mixed private callers remain diagnosed" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn collect(memory: std.mem.Allocator) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 1) catch {};
        \\    return out.items;
        \\}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn safe(self: *Model) []u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\pub fn external(memory: std.mem.Allocator) []u8 {
        \\    return collect(memory);
        \\}
        \\
    );
}

test "return-arraylist-items: public allocator helper remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\pub fn collect(memory: std.mem.Allocator) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 1) catch {};
        \\    return out.items;
        \\}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn safe(self: *Model) []u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: mixed arena and heap mutations remain diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context, memory: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 1) catch {};
        \\        out.append(memory, 2) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: allocator-like method on non-arena field remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FauxArena = struct {
        \\    fn allocator(_: *FauxArena) std.mem.Allocator {
        \\        return std.heap.page_allocator;
        \\    }
        \\};
        \\const Context = struct {
        \\    arena: FauxArena,
        \\    fn render(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 1) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: unrelated pointer does not prove allocator lifetime" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const State = struct {};
        \\fn render(_: *State, memory: std.mem.Allocator) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 1) catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: arbitrary model pointer does not prove arena lifetime" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Model = struct { arena: std.heap.ArenaAllocator };
        \\fn render(model: *Model) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(model.arena.allocator(), 1) catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: callback context field initialized from declared arena" {
    // This arm settles a question it cannot answer from the file's own
    // spelling, so it needs the same real type engine the private-helper
    // arm does.  Two of its proofs read the SCOPE a site is written in:
    // the enclosing function of a `….alloc = …` write, and the
    // enclosing function of the `.ctx = @ptrCast(&…)` that hands the
    // context to the callback.  Both are read through the engine's own
    // scope index rather than a span or a name walk, so `self.<field>`
    // resolves against the receiver that function actually declares and
    // a write inside a nested function is read against the nested
    // function's own receiver.  No resolver, and the question is open, so
    // the site is reported — which is exactly what the untyped harness
    // did here, and reporting on an arena-backed registration is not a
    // statement about the arena.
    //
    // The source below is the consumer contract's own: a model that
    // initialises its context field from its declared arena, registers
    // the callback with a pointer to that context, and never writes the
    // field again.  Only the harness moved.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const CompletionCtx = struct { alloc: std.mem.Allocator };
        \\fn candidates(ctx: *const anyopaque) []u8 {
        \\    const cctx: *const CompletionCtx = @ptrCast(@alignCast(ctx));
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(cctx.alloc, 1) catch {};
        \\    return out.items;
        \\}
        \\const Provider = struct {
        \\    ctx: *const anyopaque,
        \\    candidates: *const fn (*const anyopaque) []u8,
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    completion_ctx: CompletionCtx,
        \\    provider: Provider,
        \\    fn init(self: *Model) void {
        \\        self.* = .{
        \\            .arena = .init(std.heap.page_allocator),
        \\            .completion_ctx = undefined,
        \\            .provider = undefined,
        \\        };
        \\        self.completion_ctx = .{ .alloc = self.arena.allocator() };
        \\        self.provider = .{
        \\            .ctx = @ptrCast(&self.completion_ctx),
        \\            .candidates = candidates,
        \\        };
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: mixed callback context writes remain diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const CompletionCtx = struct { alloc: std.mem.Allocator };
        \\fn candidates(ctx: *const anyopaque) []u8 {
        \\    const cctx: *const CompletionCtx = @ptrCast(@alignCast(ctx));
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(cctx.alloc, 1) catch {};
        \\    return out.items;
        \\}
        \\const Provider = struct {
        \\    ctx: *const anyopaque,
        \\    candidates: *const fn (*const anyopaque) []u8,
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    completion_ctx: CompletionCtx,
        \\    provider: Provider,
        \\    fn init(self: *Model) void {
        \\        self.completion_ctx = .{ .alloc = self.arena.allocator() };
        \\        self.provider = .{
        \\            .ctx = @ptrCast(&self.completion_ctx),
        \\            .candidates = candidates,
        \\        };
        \\    }
        \\    pub fn replaceContext(self: *Model, memory: std.mem.Allocator) void {
        \\        self.completion_ctx = .{ .alloc = memory };
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: externally supplied callback context remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const CompletionCtx = struct { alloc: std.mem.Allocator };
        \\fn candidates(ctx: *const anyopaque) []u8 {
        \\    const cctx: *const CompletionCtx = @ptrCast(@alignCast(ctx));
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(cctx.alloc, 1) catch {};
        \\    return out.items;
        \\}
        \\const Provider = struct {
        \\    ctx: *const anyopaque,
        \\    candidates: *const fn (*const anyopaque) []u8,
        \\};
        \\pub fn install(ctx: *const anyopaque) Provider {
        \\    return .{ .ctx = ctx, .candidates = candidates };
        \\}
        \\
    );
}

test "return-arraylist-items: heap capacity growth after an arena allocation remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn ensureHeap(self: *Context, heap: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.ensureTotalCapacity(heap, 64) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a heap allocator reaching a charged growth entry point is diagnosed" {
    // Three real `Aligned` entry points that take the allocator first.
    // The fourth in the file is `print`, covered on its own below with
    // the Bounded control that must NOT be charged beside it.
    try testing.expectCount(check, R, 3,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn unused(self: *Context, heap: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.ensureUnusedCapacity(heap, 8) catch {};
        \\        return out.items;
        \\    }
        \\    fn one(self: *Context, heap: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.addOne(heap) catch {};
        \\        return out.items;
        \\    }
        \\    fn many(self: *Context, heap: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.addManyAsSlice(heap, 2) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: print takes the allocator and reallocates the buffer" {
    // `print(self, gpa, fmt, args)` calls `ensureUnusedCapacity(gpa, …)`
    // first (array_list.zig:1042), so the heap it is handed grows the
    // very buffer the arena grew before it.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context, heap: std.mem.Allocator, raw: []const u8) ![]u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.arena.allocator(), 'x');
        \\        try out.print(heap, "{s}", .{raw});
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a Bounded entry point takes no allocator and cannot reallocate" {
    // `addOneBounded(self)` (array_list.zig:1290) has no allocator
    // parameter at all, so charging it would read the FIRST argument it
    // is written with as the buffer's owner — and refuse a site the
    // rule's own contract discharges.  Writing through the slot it
    // returns touches an element, not the header.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context) ![]u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.arena.allocator(), 'x');
        \\        const slot = try out.addOneBounded();
        \\        slot.* = 'y';
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a Bounded entry point cannot stand in for the charged print" {
    // The same site with `printBounded`, which writes into capacity
    // already reserved (array_list.zig:1059): still quiet, and for the
    // same reason — no allocator reaches the buffer.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context) ![]u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.arena.allocator(), 'x');
        \\        try out.printBounded("{s}", .{"yy"});
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an escaped list helper that rebinds the list onto the heap remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn rebind(out: *std.ArrayList(u8), heap: std.mem.Allocator) void {
        \\    out.* = .empty;
        \\    out.ensureTotalCapacity(heap, 64) catch return;
        \\    out.appendAssumeCapacity('y');
        \\}
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn helperHeap(self: *Context, heap: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        rebind(&out, heap);
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a non-list type with an allocator-taking append is not an arena-backed list" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Sink = struct {
        \\    items: []u8,
        \\    fn append(self: *Sink, memory: std.mem.Allocator, byte: u8) !void {
        \\        _ = memory;
        \\        self.items = try std.heap.page_allocator.realloc(self.items, self.items.len + 1);
        \\        self.items[self.items.len - 1] = byte;
        \\    }
        \\};
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context) []u8 {
        \\        var out: Sink = .{ .items = &.{} };
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a file-local type named ArrayList is not the standard list" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const ArrayList = struct {
        \\    items: []u8,
        \\    fn append(self: *ArrayList, memory: std.mem.Allocator, byte: u8) !void {
        \\        _ = memory;
        \\        self.items = try std.heap.page_allocator.realloc(self.items, self.items.len + 1);
        \\        self.items[self.items.len - 1] = byte;
        \\    }
        \\};
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context) []u8 {
        \\        var out: ArrayList = .{ .items = &.{} };
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a list bound to a foreign buffer is not an arena-backed list" {
    // `initBuffer(&buf)` (array_list.zig:615) names the array as it is —
    // a stack or static buffer that dies with this frame — and
    // `fromOwnedSlice` takes over a slice whose owner this file never
    // proves.  Neither takes an allocator, so there is nothing to charge;
    // what the walk owes the site is a refusal.  The ANNOTATED declaration
    // is what made this reachable: the type is proved there, so the walk
    // used to reach the initializer, find no constructor it recognises,
    // and move on with nothing charged and nothing refused.
    try testing.expectCount(check, R, 2,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn fromStack(self: *Context) []const u8 {
        \\        _ = self;
        \\        var buffer: [32]u8 = undefined;
        \\        var out: std.ArrayList(u8) = .initBuffer(&buffer);
        \\        return out.items;
        \\    }
        \\    fn fromSlice(self: *Context, existing: []const u8) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .fromOwnedSlice(existing);
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a rebound header onto a foreign buffer is refused too" {
    // The same constructors reached through `out = …`, which rebinds the
    // header rather than declaring it.  The spelling with the type in
    // front is the one a file writes; both must refuse.
    try testing.expectCount(check, R, 2,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn rebindStack(self: *Context) []const u8 {
        \\        _ = self;
        \\        var buffer: [32]u8 = undefined;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out = std.ArrayList(u8).initBuffer(&buffer);
        \\        return out.items;
        \\    }
        \\    fn rebindSlice(self: *Context, existing: []const u8) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out = std.ArrayList(u8).fromOwnedSlice(existing);
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an arena-backed list still starts quiet from a literal header" {
    // The control for the two refusals above: the same declaration shape,
    // the same rebound header, with nothing foreign bound to them.  If
    // the refusal were reaching past the constructor it read, these would
    // go with them.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn declared(self: *Context) []const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\    fn rebound(self: *Context) ![]const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out = try std.ArrayList(u8).initCapacity(self.arena.allocator(), 8);
        \\        out.append(self.arena.allocator(), 'y') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an arena-owned list reallocated by its own arena stays quiet" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn growTotal(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.ensureTotalCapacity(self.arena.allocator(), 64) catch {};
        \\        return out.items;
        \\    }
        \\    fn growUnused(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.ensureUnusedCapacity(self.arena.allocator(), 8) catch {};
        \\        return out.items;
        \\    }
        \\    fn growOne(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out.addOne(self.arena.allocator()) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: aliased standard list spellings keep the arena proof" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Bytes = std.ArrayList(u8);
        \\const Packed = std.ArrayListAligned(u8, std.mem.Alignment.fromByteUnits(16));
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn aliased(self: *Context) []u8 {
        \\        var out: Bytes = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\    fn aligned(self: *Context) []align(16) u8 {
        \\        var out: Packed = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: the module-path and unmanaged spellings keep the arena proof" {
    // Both spellings carry a generic argument group after the name that owns
    // it.  Reading the group as if it were the tail of the path would leave
    // `std.array_list` unqualified and drop every such list out of the proof.
    // The first method is deliberately not named `packed`: that is a Zig
    // keyword, and `fn packed(…)` would not parse at all.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn modulePath(self: *Context) []align(16) u8 {
        \\        var out: std.array_list.Aligned(u8, std.mem.Alignment.fromByteUnits(16)) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\    fn unmanaged(self: *Context) []u8 {
        \\        var out: std.ArrayListUnmanaged(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: the private helper closure keeps the arena proof for arena growth" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Allocator = std.mem.Allocator;
        \\fn own(memory: Allocator, raw: []const u8) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, raw) catch {};
        \\    out.ensureTotalCapacity(memory, raw.len) catch {};
        \\    return out.items;
        \\}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Model, raw: []const u8) []const u8 {
        \\        return own(self.arena.allocator(), raw);
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a helper reached only by direct calls keeps the arena proof" {
    // The control for the reflection boundary below: `grow` is called
    // once, spelled out, and every allocator that can reach its buffer
    // is `self.arena`.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn grow(memory: std.mem.Allocator, raw: []const u8) []const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.appendSlice(memory, raw) catch {};
        \\        return out.items;
        \\    }
        \\    fn render(self: *Model, raw: []const u8) []const u8 {
        \\        return Model.grow(self.arena.allocator(), raw);
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a reflected entry into the helper is the boundary, not a verdict" {
    // `hidden` reaches the same helper through `@field(@This(), "grow")`.
    // That binds the callee to a local named `f`, so the call is spelled
    // with the LOCAL's name: it is no identifier reference to `grow` and
    // no call any name census can match, while the heap allocator it
    // hands over is real.  The site is reported because the argument
    // that reached `grow` is unknown here — not because a reflected call
    // is unsafe.  The reflected path itself is not claimed either way.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn grow(memory: std.mem.Allocator, raw: []const u8) []const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.appendSlice(memory, raw) catch {};
        \\        return out.items;
        \\    }
        \\    fn render(self: *Model, raw: []const u8) []const u8 {
        \\        return Model.grow(self.arena.allocator(), raw);
        \\    }
        \\    fn hidden(self: *Model, heap: std.mem.Allocator, raw: []const u8) []const u8 {
        \\        _ = self;
        \\        const f = @field(@This(), "grow");
        \\        return f(heap, raw);
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an arena handed in as a typed parameter owns the backing storage" {
    // The parameter's own type node IS the declaration: a
    // `*std.heap.ArenaAllocator` argument can only have come from one.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context, memory: *std.heap.ArenaAllocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a by-value arena parameter is not the arena it was copied from" {
    // A copied header frees the ORIGINAL arena when it is deinited, so
    // the copy is not the arena and its allocator proves nothing about
    // what the caller keeps.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context, memory: std.heap.ArenaAllocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a lookalike arena-shaped parameter is not the standard arena" {
    // A project allocator of the same shape owns what it hands out.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Pool = struct {
        \\    buffer: [64]u8,
        \\    used: usize,
        \\    pub fn allocator(self: *Pool) std.mem.Allocator {
        \\        _ = self;
        \\        return std.heap.page_allocator;
        \\    }
        \\};
        \\const Context = struct {
        \\    pub fn render(memory: *Pool) []const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: escaping a different list does not void the arena proof" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn rebind(other: *std.ArrayList(u8), heap: std.mem.Allocator) void {
        \\    other.* = .empty;
        \\    other.ensureTotalCapacity(heap, 64) catch return;
        \\    other.appendAssumeCapacity('y');
        \\}
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context, heap: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        var other: std.ArrayList(u8) = .empty;
        \\        rebind(&other, heap);
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a list rebound onto a heap allocator before the return remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context, heap: std.mem.Allocator, n: usize) ![]u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        out = try std.ArrayList(u8).initCapacity(heap, n);
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a list rebound through the same arena stays quiet" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context, n: usize) ![]u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out = try std.ArrayList(u8).initCapacity(self.arena.allocator(), n);
        \\        out.appendAssumeCapacity('x');
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a memoised map value is a borrow, not a lost header" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Cache = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    fn membershipOf(self: *Cache, key: []const u8) []const []const u8 {
        \\        if (self.members.get(key)) |cached| return cached.items;
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a keyed map value is a borrow too" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Cache = struct {
        \\    members: std.StringHashMapUnmanaged([]const u8, std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    fn membershipOf(self: *Cache, key: []const u8) []const []const u8 {
        \\        if (self.members.get(key)) |cached| return cached.items;
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: growing a borrowed map value still needs a transfer" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Cache = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    fn membershipOf(self: *Cache, gpa: std.mem.Allocator, key: []const u8) ![]const []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            try cached.append(gpa, "extra");
        \\            return cached.items;
        \\        }
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an accessor that hands over the only header still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Cache = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    fn popMembership(self: *Cache) ?[]const []const u8 {
        \\        if (self.members.pop()) |owned| return owned.items;
        \\        return null;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a map local to the function still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn membershipOf(gpa: std.mem.Allocator, key: []const u8) ![]const []const u8 {
        \\    var members: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty;
        \\    defer members.deinit(gpa);
        \\    try members.put(gpa, key, .fromOwnedSlice(&.{}));
        \\    if (members.get(key)) |cached| return cached.items;
        \\    return &.{};
        \\}
        \\
    );
}

test "return-arraylist-items: writing to the map between capture and return still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Cache = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    fn membershipOf(self: *Cache, gpa: std.mem.Allocator, key: []const u8) ![]const []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            try self.members.put(gpa, "other", .fromOwnedSlice(&.{}));
        \\            return cached.items;
        \\        }
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a project get of a non-map field is unproven" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Memo = struct {
        \\    fn get(_: *Memo, _: []const u8) ?std.ArrayListUnmanaged([]const u8) {
        \\        return null;
        \\    }
        \\};
        \\const Cache = struct {
        \\    memo: Memo,
        \\    fn membershipOf(self: *Cache, key: []const u8) []const []const u8 {
        \\        if (self.memo.get(key)) |cached| return cached.items;
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a for payload over the map's values still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Cache = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    fn firstMembership(self: *Cache) []const []const u8 {
        \\        for (self.members.values()) |cached| return cached.items;
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: every top-level list spelling keeps the arena proof" {
    // The two `ArrayListAligned` spellings are declared by `std.zig`
    // ITSELF (`std.zig`:55,57), so they are top-level names and are read
    // as such.  Each carries a two-argument group, and the whole group is
    // what the path walk steps over.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn aligned(self: *Context) []align(16) u8 {
        \\        var out: std.ArrayListAligned(u8, std.mem.Alignment.fromByteUnits(16)) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\    fn alignedUnmanaged(self: *Context) []align(16) u8 {
        \\        var out: std.ArrayListAlignedUnmanaged(u8, std.mem.Alignment.fromByteUnits(16)) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a top-level std.Aligned names no declaration and still fires" {
    // `Aligned` is declared inside `std/array_list.zig` and nowhere at
    // the top level, so `std.Aligned` names nothing.  Reading the name
    // without asking WHICH namespace it was reached through would let it
    // pass for the top-level list it is not.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context) []align(16) u8 {
        \\        var out: std.Aligned(u8, std.mem.Alignment.fromByteUnits(16)) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: the managed array_list type is not the list this proof discharges" {
    // `array_list.Managed` holds its allocator in the header, so its
    // `append` carries the ITEM where this rule's charge reads an
    // allocator.  It is refused rather than read through the unmanaged
    // names, and the site stays diagnosed.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context) []u8 {
        \\        var out: std.array_list.Managed(u8) = .empty;
        \\        out.append('x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an arena type reached through an alias keeps the proof" {
    // The alias is a `const` at file scope, so the walk follows its own
    // initializer and lands on the same declaration the direct spelling
    // names.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Arena = std.heap.ArenaAllocator;
        \\const Context = struct {
        \\    arena: Arena,
        \\    fn render(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a container that re-exports the arena name is not read past" {
    // `heap.ArenaAllocator` really does reach the standard arena, but
    // only by a walk through a CONTAINER's own declarations, and this
    // rule has no seam for one.  A question that might be about a
    // container is declined rather than answered from the file's top
    // level behind it — which is a refusal, not a grant.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const heap = struct {
        \\    pub const ArenaAllocator = std.heap.ArenaAllocator;
        \\};
        \\const Context = struct {
        \\    arena: heap.ArenaAllocator,
        \\    fn render(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a std rebound to another module is not the standard library" {
    // The `std` this body writes is the LOCAL `const`, which shadows the
    // file's import for every use inside it — so it names that module and
    // nothing proves the buffer behind `other.ArrayList` is the standard
    // list's.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn render(allocator: std.mem.Allocator) []u8 {
        \\    const std = @import("other");
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(allocator, 'x') catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: a standard map of a project list is not a borrowed value" {
    // The container here IS a standard map, so this is the control that
    // the map's own names are not what refuses the site — what refuses it
    // is the VALUE group, which is the project list rather than the
    // standard one.  `StringArrayHashMap*` takes that value alone, so it
    // is the FIRST argument the group is read at.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FauxList = struct { items: []const u8 };
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(FauxList) = .empty,
        \\    fn first(self: *Memo) []const u8 {
        \\        if (self.members.get("k")) |cached| return cached.items;
        \\        return &.{};
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a full-capacity comparison that growth invalidates still fires" {
    // The comparison held where it was written and one `append` after it
    // moved the buffer.  The proof is about what the RETURN names, so a
    // statement that changes it in between withdraws it.
    try testing.expectFires(check, R,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    assert(list.items.len == list.capacity);
        \\    try list.append('x');
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: a full-capacity guard immediately before the return stays quiet" {
    // Nothing stands between the comparison and the `return` except the
    // read of the very slice the comparison settled, so the proof still
    // holds where it is asked about.
    try testing.expectNoFire(check,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try fill(&list);
        \\    if (list.items.len == list.capacity) return list.items;
        \\    return list.toOwnedSlice();
        \\}
        \\
    );
}

test "return-arraylist-items: another list's growth does not void this list's full-capacity proof" {
    // The staleness question is asked about THIS receiver.  `other` grows
    // its own buffer, and with no alias reaching `list` it changes nothing
    // about what `list` names — so the comparison stays a proof.
    try testing.expectNoFire(check,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    var other = try std.ArrayList(u8).initCapacity(allocator, 8);
        \\    try other.append('x');
        \\    assert(list.items.len == list.capacity);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: growth through an address taken before the comparison still fires" {
    // `alias` is a second name for `list`'s header, taken BEFORE the
    // comparison settled.  A growth written through that name is
    // invisible to a scan that only knows the name the `return` uses, so
    // the escape and the mutation are two separate questions and only the
    // pair of them invalidates the comparison.
    try testing.expectFires(check, R,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    const alias = &list;
        \\    assert(list.items.len == list.capacity);
        \\    try alias.append(allocator, 'x');
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: handing the settled slice to a free still fires" {
    // `gpa.free(list.items)` releases exactly the block the comparison
    // proved fully covered.  Reading the header afterwards says nothing
    // about bytes that are no longer allocated, so allowing every
    // `recv.items` mention as a read would accept this.
    try testing.expectFires(check, R,
        \\fn build(gpa: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
        \\    assert(list.items.len == list.capacity);
        \\    gpa.free(list.items);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: a by-value map argument lets a releasing helper reach the capture" {
    // Passing the map by value copies its header, not its entries' buffers.
    // This bypasses the existing address-of refusal.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: []const u8) []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            visit(self.members, self.gpa);
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a by-value map argument to a neutral helper keeps the borrow" {
    // Same helper name and argument path. Only the callee body changes.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\fn visit(members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8))) usize {
        \\    return members.count();
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: []const u8) []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            _ = visit(self.members);
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: incoming containers are not proved independent" {
    // The caller can pass two headers for the same entry storage.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    other: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: []const u8) []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            visit(self.other, self.gpa);
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a body-local arena deinited before the return still fires" {
    // An unchanged lifetime control, not a reproduction of the reviewer's
    // root/local shadow counter. The local arena dies before the view escapes.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\const Grower = struct {
        \\    fn render(allocator: std.mem.Allocator) []const u8 {
        \\        var arena = std.heap.ArenaAllocator.init(allocator);
        \\        defer arena.deinit();
        \\
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(arena.allocator(), 'x') catch unreachable;
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a header alias assigned from the borrowed container still fires" {
    // `self.other` is a DIFFERENT FIELD of the SAME type, so neither a
    // path question nor a type question can tell it apart from
    // `self.members` -- and both of those spellings answer "disjoint".
    // The assignment is the only statement that connects them: it copies
    // the unmanaged map header, so from that line on `self.other` names
    // the very entries the capture came from and the releasing call
    // through it frees exactly the buffer `cached` holds.
    //
    // The one-statement difference from the `self.other` control below is
    // what this row is about.  Without the assignment that control's
    // storage really is separate and must stay quiet.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    other: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: []const u8) []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            self.other = self.members;
        \\            visit(self.other, self.gpa);
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: an incoming allocator callback is not proved harmless" {
    // Fresh arguments do not prove that an unresolved callback has no other effects.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\fn make(gpa: std.mem.Allocator) !std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) {
        \\    var out: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty;
        \\    errdefer out.deinit(gpa);
        \\    var entry = try std.ArrayList(u8).initCapacity(gpa, 9);
        \\    errdefer entry.deinit(gpa);
        \\    try entry.append(gpa, 'x');
        \\    try out.put(gpa, true, entry);
        \\    return out;
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: bool) []const u8 {
        \\        var other = make(self.gpa) catch unreachable;
        \\        if (self.members.get(key)) |cached| {
        \\            visit(other, self.gpa);
        \\            other.deinit(self.gpa);
        \\            return cached.items;
        \\        }
        \\        visit(other, self.gpa);
        \\        other.deinit(self.gpa);
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a factory that stores the borrowed header still fires" {
    // One parameter is the whole difference from the row above, and it turns
    // the fresh table into a window onto the captured entry.  `borrowed` is
    // the entry's own header copied out of `self.members`, so `visit` walks
    // storage that really is fresh -- and frees the entry's buffer anyway,
    // because the value stored under the fresh key IS that header.  The map's
    // own `deinit` then releases the table alone and destroys the last name
    // the value had, which is what makes the two lines read so tidily.
    //
    // The argument path, the argument type and the callee are identical to
    // the quiet row, so all three of those questions answer "disjoint" here.
    // The header is what crosses, and a report here is the only correct
    // answer: the slice handed back is freed before it is handed back.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\fn make(
        \\    gpa: std.mem.Allocator,
        \\    borrowed: std.ArrayList(u8),
        \\) !std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) {
        \\    var out: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty;
        \\    errdefer out.deinit(gpa);
        \\    try out.put(gpa, true, borrowed);
        \\    return out;
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: bool) []const u8 {
        \\        const borrowed = self.members.get(key) orelse return "";
        \\        var other = make(self.gpa, borrowed) catch unreachable;
        \\        if (self.members.get(key)) |cached| {
        \\            visit(other, self.gpa);
        \\            other.deinit(self.gpa);
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: concrete SDK allocator and fresh storage keep the borrow" {
    // The released container here comes out of `std.heap.page_allocator`,
    // a concrete SDK allocator that is not the receiver's, while the
    // captured entry is still a block the receiver's own allocator holds.
    // Two sides, two separate issuances -- and the row is still quiet,
    // because the reason has never been the allocator: `make` allocated
    // the buffer the release reaches, and `visit` walks only the map it
    // built.
    //
    // The word is not the argument.  Two separately constructed debug
    // allocators would separate the storage just as well, and a container
    // that ALIASED the capture would still dangle with this allocator in
    // place -- which is what the test one below it exists to keep saying.
    // So nothing here may be answered by an allocator's name, and nothing
    // may treat "a different allocator" as a licence to skip the question.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\fn make(gpa: std.mem.Allocator) !std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) {
        \\    var out: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty;
        \\    errdefer out.deinit(gpa);
        \\    var entry = try std.ArrayList(u8).initCapacity(gpa, 9);
        \\    errdefer entry.deinit(gpa);
        \\    try entry.append(gpa, 'x');
        \\    try out.put(gpa, true, entry);
        \\    return out;
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: bool) []const u8 {
        \\        var other = make(std.heap.page_allocator) catch unreachable;
        \\        if (self.members.get(key)) |cached| {
        \\            visit(other, std.heap.page_allocator);
        \\            other.deinit(std.heap.page_allocator);
        \\            return cached.items;
        \\        }
        \\        visit(other, std.heap.page_allocator);
        \\        other.deinit(std.heap.page_allocator);
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a zero-argument callee that releases the globally held capture still fires" {
    // The releasing call passes NOTHING.  Its callee's parameter list is
    // empty, so there is no argument path, no argument type and no value
    // to follow -- and the callee's body still returns the captured
    // buffer to the allocator that issued it, through a file-scope global
    // that `line` assigned the capture to two statements earlier.
    //
    // That is the question this pair poses: a zero-parameter call is a
    // real call, and "nothing was passed" is a fact about the parameter
    // list, not about whether anything was released.  The report here is
    // the only correct answer -- the slice is freed before it is handed
    // back -- and the test below it has an identical call, an identical
    // name and a body that frees nothing, which must stay quiet.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\var held: std.ArrayList(u8) = .empty;
        \\var released_by: std.mem.Allocator = undefined;
        \\
        \\fn visit() void {
        \\    released_by.free(held.allocatedSlice());
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: []const u8) []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            held = cached;
        \\            released_by = self.gpa;
        \\            visit();
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: a zero-argument callee that only returns a literal stays quiet" {
    // Same callee name, same empty parameter list, same receiver, same
    // field names, same single `.items` return site, same std map type as
    // the row above -- and a body that is a bare literal.  It takes no
    // allocator, names no global and frees nothing.
    //
    // So the two rows differ in no way a name, an arity, a receiver or a
    // call position can read; the only thing left is the callee's own
    // body.  A rule that answered "the callee has no parameters, so I
    // cannot follow what it releases" would refuse this row too and would
    // be wrong about it: nothing is released here at all.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\fn visit() usize {
        \\    return 7;
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: []const u8) []const u8 {
        \\        if (self.members.get(key)) |cached| {
        \\            _ = visit();
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: concrete SDK callback still refuses copied entry buffers" {
    // The factory is handed the captured entry's own header and stores it
    // under a fresh key, so the container `visit` walks owns a table that is
    // entirely its own and a value that is not its own at all.  Every
    // allocator operand below is now `std.heap.page_allocator` -- a
    // concrete SDK allocator, not the receiver's incoming `self.gpa` -- and
    // the row is still LOUD.
    //
    // That is the whole point of this block beside the quiet page-allocator
    // row above it.  Two separately issued `DebugAllocator`s would separate
    // the storage just as well, and a container that ALIASED the capture
    // would still hand out a dangling slice with `page_allocator` in place,
    // which is this row.  So an allocator's name can be the answer in
    // neither direction, and a fresh factory is not fresh storage: `make`
    // performs a real SDK allocation for the TABLE, before the capture, and
    // none of that says anything about the buffer the stored header names.
    //
    // `self.gpa` is still a field of `Memo` and is still never read on this
    // path, so nothing here may be answered by the receiver's allocator
    // name, nor by any field's name.  Only the origin of the stored header
    // decides it, and the report is the only correct answer: the bytes
    // behind the view handed back were released before they were handed
    // back.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\fn make(
        \\    gpa: std.mem.Allocator,
        \\    borrowed: std.ArrayList(u8),
        \\) !std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) {
        \\    var out: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty;
        \\    errdefer out.deinit(gpa);
        \\    try out.put(gpa, true, borrowed);
        \\    return out;
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8)) = .empty,
        \\    gpa: std.mem.Allocator,
        \\
        \\    fn line(self: *Memo, key: bool) []const u8 {
        \\        const borrowed = self.members.get(key) orelse return "";
        \\        var other = make(std.heap.page_allocator, borrowed) catch unreachable;
        \\        if (self.members.get(key)) |cached| {
        \\            visit(other, std.heap.page_allocator);
        \\            other.deinit(std.heap.page_allocator);
        \\            return cached.items;
        \\        }
        \\        return "";
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: owner-managed membership cache borrows SDK list storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Wiring = struct {
        \\    pub const NamedModuleMap = struct {
        \\        memberships: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\        pub const ModuleWiring = struct { root: []const u8 };
        \\        pub fn deinit(self: *NamedModuleMap, gpa: std.mem.Allocator) void {
        \\            for (self.memberships.values()) |*paths| {
        \\                for (paths.items) |path| gpa.free(path);
        \\                paths.deinit(gpa);
        \\            }
        \\            self.memberships.deinit(gpa);
        \\        }
        \\        pub fn membershipOf(self: *NamedModuleMap, gpa: std.mem.Allocator, identity: []const u8) ![]const []const u8 {
        \\            if (self.memberships.get(identity)) |cached| return cached.items;
        \\            var scratch = std.heap.ArenaAllocator.init(gpa);
        \\            defer scratch.deinit();
        \\            var reached: std.ArrayList([]const u8) = .empty;
        \\            try reached.append(scratch.allocator(), identity);
        \\            const owned = try gpa.alloc([]const u8, reached.items.len);
        \\            errdefer gpa.free(owned);
        \\            for (owned, reached.items) |*slot, path| slot.* = try gpa.dupe(u8, path);
        \\            try self.memberships.put(gpa, identity, .fromOwnedSlice(owned));
        \\            return owned;
        \\        }
        \\    };
        \\};
    );
}

test "return-arraylist-items: a membership method still reports its fresh underfilled local" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const NamedModuleMap = struct {
        \\    memberships: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    pub fn membershipOf(self: *NamedModuleMap, gpa: std.mem.Allocator, identity: []const u8) ![]const []const u8 {
        \\        if (self.memberships.get(identity)) |cached| return cached.items;
        \\        var fresh = try std.ArrayList([]const u8).initCapacity(gpa, 64);
        \\        fresh.appendAssumeCapacity(identity);
        \\        return fresh.items;
        \\    }
        \\};
    );
}

test "return-arraylist-items: unrelated large bodies do not exhaust a small local proof" {
    const gpa = std.testing.allocator;
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa, "const std = @import(\"std\");\nfn unrelated() void {\n");
    for (0..20000) |_| try source.appendSlice(gpa, "_ = 1 + 2;\n");
    try source.appendSlice(gpa,
        \\}
        \\pub fn local(gpa: std.mem.Allocator) ![]u8 {
        \\    var out = try std.ArrayList(u8).initCapacity(gpa, 64);
        \\    out.appendAssumeCapacity(1);
        \\    return out.items;
        \\}
    );
    var problems = try testing.runRule(gpa, check, source.items);
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
}

test "return-arraylist-items: a genuinely oversized questioned body retains the work bound" {
    const gpa = std.testing.allocator;
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa,
        \\const std = @import("std");
        \\pub fn oversized(gpa: std.mem.Allocator) ![]u8 {
        \\    var out = try std.ArrayList(u8).initCapacity(gpa, 64);
        \\
    );
    for (0..20000) |_| try source.appendSlice(gpa, "_ = 1 + 2;\n");
    try source.appendSlice(gpa, "    return out.items;\n}\n");
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRule(gpa, check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.arena_proof_steps, diagnostic.limit);
    try std.testing.expectEqual(call_summary.actual_query_work_limit, diagnostic.limit_value);
    try std.testing.expectEqual(call_summary.actual_query_work_limit, diagnostic.reached);
    try std.testing.expectEqualStrings("oversized", diagnostic.function.slice());
    try std.testing.expectEqualStrings("return out.items;\n}\n", source.items[diagnostic.byte..]);
}

/// Resolve the actual SDK unmanaged-list container. Managed lists carry an
/// allocator in their header and require a different growth proof.
fn actualStandardList(
    resolver: *resolver_mod.TypeResolver,
    index: *DeclIndex,
    node: Ast.Node.Index,
) ProofError!bool {
    const actual = (try resolver.containerOfNode(node)) orelse return false;
    const handle = actual.scope_handle.handle;
    if (!try resolver.declaredInToolchainFile(handle, "/std/array_list.zig")) return false;
    const tree = &handle.document.tree;
    var buffer: [2]Ast.Node.Index = undefined;
    const container = tree.fullContainerDecl(&buffer, actual.scope_handle.toNode()) orelse return false;
    var items = false;
    var capacity = false;
    for (container.ast.members) |member| {
        try index.spend(index.return_token orelse 0);
        const field = tree.fullContainerField(member) orelse continue;
        const name = tree.tokenSlice(field.ast.main_token);
        if (std.mem.eql(u8, name, "allocator")) return false;
        if (std.mem.eql(u8, name, "items")) items = true;
        if (std.mem.eql(u8, name, "capacity")) capacity = true;
    }
    return items and capacity;
}

test "return-arraylist-items: unrelated large AST leaves an owner-managed SDK borrow provable" {
    const gpa = std.testing.allocator;
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa,
        \\const std = @import("std");
        \\const NamedModuleMap = struct {
        \\    memberships: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
        \\    pub fn membershipOf(self: *NamedModuleMap, identity: []const u8) []const []const u8 {
        \\        if (self.memberships.get(identity)) |cached| return cached.items;
        \\        return &.{};
        \\    }
        \\};
        \\fn unrelated() void {
        \\
    );
    for (0..20000) |_| try source.appendSlice(gpa, "_ = 1 + 2;\n");
    try source.appendSlice(gpa, "}\n");
    var problems = try testing.runRuleTyped(gpa, check, source.items);
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

/// A method whose list grows through an allocator reached by `hops` local
/// aliases of the receiver's own arena.
fn aliasChainSource(gpa: std.mem.Allocator, hops: usize) !std.ArrayListUnmanaged(u8) {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    errdefer source.deinit(gpa);
    try source.appendSlice(gpa,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context) []const u8 {
        \\        const a0 = self.arena.allocator();
        \\
    );
    for (1..hops + 1) |i| try source.print(gpa, "        const a{d} = a{d};\n", .{ i, i - 1 });
    try source.print(gpa,
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(a{d}, 'x') catch {{}};
        \\        return out.items;
        \\    }}
        \\}};
        \\
    , .{hops});
    return source;
}

test "return-arraylist-items: a shallow allocator alias chain still proves the arena" {
    const gpa = std.testing.allocator;
    var source = try aliasChainSource(gpa, 3);
    defer source.deinit(gpa);
    try testing.expectNoFire(check, source.items);
}

test "return-arraylist-items: an allocator alias chain past the depth bound is unfinished, not unproven" {
    const gpa = std.testing.allocator;
    var source = try aliasChainSource(gpa, 12);
    defer source.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRule(gpa, check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.arena_proof_depth, diagnostic.limit);
    try std.testing.expectEqual(@as(u32, allocator_depth_limit), diagnostic.limit_value);
    try std.testing.expectEqualStrings("render", diagnostic.function.slice());
}

/// `levels` private helpers that each forward their allocator formal to the
/// one below, the bottom one growing the returned list; the only caller
/// hands the top one the receiver's own arena.
fn privateCallChainSource(gpa: std.mem.Allocator, levels: usize) !std.ArrayListUnmanaged(u8) {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    errdefer source.deinit(gpa);
    try source.appendSlice(gpa,
        \\const std = @import("std");
        \\const Allocator = std.mem.Allocator;
        \\fn l0(memory: Allocator) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 'x') catch {};
        \\    return out.items;
        \\}
        \\
    );
    for (1..levels) |i| try source.print(
        gpa,
        "fn l{d}(memory: Allocator) []const u8 {{\n    return l{d}(memory);\n}}\n",
        .{ i, i - 1 },
    );
    try source.print(gpa,
        \\const Model = struct {{
        \\    arena: std.heap.ArenaAllocator,
        \\    fn evaluate(self: *Model) void {{
        \\        _ = l{d}(self.arena.allocator());
        \\    }}
        \\}};
        \\
    , .{levels - 1});
    return source;
}

test "return-arraylist-items: a short private call chain still proves the arena" {
    const gpa = std.testing.allocator;
    var source = try privateCallChainSource(gpa, 3);
    defer source.deinit(gpa);
    try testing.expectNoFireTyped(check, source.items);
}

test "return-arraylist-items: a private call chain past the depth bound is unfinished, not unproven" {
    const gpa = std.testing.allocator;
    var source = try privateCallChainSource(gpa, 9);
    defer source.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRuleTyped(gpa, check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.arena_proof_depth, diagnostic.limit);
    try std.testing.expectEqual(@as(u32, allocator_depth_limit), diagnostic.limit_value);
    try std.testing.expectEqualStrings("l0", diagnostic.function.slice());
}

/// A memo lookup whose branch hands a releasing helper a value reached
/// through `hops` local copies of an empty map, none of them the receiver's.
fn handoverChainSource(gpa: std.mem.Allocator, hops: usize) !std.ArrayListUnmanaged(u8) {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    errdefer source.deinit(gpa);
    try source.appendSlice(gpa,
        \\const std = @import("std");
        \\
        \\fn visit(
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)),
        \\    gpa: std.mem.Allocator,
        \\) void {
        \\    for (members.values()) |*entry| gpa.free(entry.allocatedSlice());
        \\}
        \\
        \\const Memo = struct {
        \\    members: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty,
        \\
        \\    fn line(self: *Memo, key: []const u8, gpa: std.mem.Allocator) []const u8 {
        \\        const d0: std.StringArrayHashMapUnmanaged(std.ArrayList(u8)) = .empty;
        \\
    );
    for (1..hops + 1) |i| try source.print(gpa, "        const d{d} = d{d};\n", .{ i, i - 1 });
    try source.print(gpa,
        \\        if (self.members.get(key)) |cached| {{
        \\            visit(d{d}, gpa);
        \\            return cached.items;
        \\        }}
        \\        return "";
        \\    }}
        \\}};
        \\
    , .{hops});
    return source;
}

test "return-arraylist-items: a releasing helper handed an unrelated local keeps the borrow" {
    const gpa = std.testing.allocator;
    var source = try handoverChainSource(gpa, 3);
    defer source.deinit(gpa);
    try testing.expectNoFireTyped(check, source.items);
}

test "return-arraylist-items: a handover chain past the depth bound is unfinished, not reaching" {
    const gpa = std.testing.allocator;
    var source = try handoverChainSource(gpa, 10);
    defer source.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRuleTyped(gpa, check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.arena_proof_depth, diagnostic.limit);
    try std.testing.expectEqual(@as(u32, receiver_depth_limit), diagnostic.limit_value);
    try std.testing.expectEqualStrings("line", diagnostic.function.slice());
}

test "return-arraylist-items: resolved foreign arena field returns a borrow" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Context = struct { storage: std.heap.ArenaAllocator };
        \\pub fn collect(context: *Context) ![]u8 {
        \\    const memory = context.storage.allocator();
        \\    var writes: std.ArrayList(u8) = .empty;
        \\    try writes.append(memory, 1);
        \\    return writes.items;
        \\}
    );
}

test "return-arraylist-items: general allocator field does not prove a borrow" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Context = struct { storage: std.mem.Allocator };
        \\pub fn collect(context: *Context) ![]u8 {
        \\    var writes: std.ArrayList(u8) = .empty;
        \\    try writes.append(context.storage, 1);
        \\    return writes.items;
        \\}
    );
}

test "return-arraylist-items: frame local resolved arena does not prove a returned borrow" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn collect(gpa: std.mem.Allocator) ![]u8 {
        \\    var storage = std.heap.ArenaAllocator.init(gpa);
        \\    defer storage.deinit();
        \\    var writes: std.ArrayList(u8) = .empty;
        \\    try writes.append(storage.allocator(), 1);
        \\    return writes.items;
        \\}
    );
}

test "return-arraylist-items: foreign arena reset refuses the returned borrow" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Context = struct { storage: std.heap.ArenaAllocator };
        \\pub fn collect(context: *Context) ![]u8 {
        \\    var writes: std.ArrayList(u8) = .empty;
        \\    try writes.append(context.storage.allocator(), 1);
        \\    _ = context.storage.reset(.free_all);
        \\    return writes.items;
        \\}
    );
}

test "return-arraylist-items: resolved general allocator local list still loses capacity" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn collect(gpa: std.mem.Allocator) ![]u8 {
        \\    var writes: std.ArrayList(u8) = .empty;
        \\    try writes.append(gpa, 1);
        \\    return writes.items;
        \\}
    );
}

test "return-arraylist-items: explicit borrowed arena pointer owns query snapshots" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Query = struct {
        \\    scratch: *std.heap.ArenaAllocator,
        \\    fn collect(self: *Query) ![]const u8 {
        \\        var windows: std.ArrayList(u8) = .empty;
        \\        try windows.append(self.scratch.allocator(), 1);
        \\        return windows.items;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Query = struct {
        \\    scratch: *std.heap.ArenaAllocator,
        \\    fn collect(self: *Query) ![]const u8 {
        \\        var windows: std.ArrayList(u8) = .empty;
        \\        try windows.append(self.scratch.allocator(), 1);
        \\        _ = self.scratch.reset(.free_all);
        \\        return windows.items;
        \\    }
        \\};
    );
}

test "return-arraylist-items: borrowed arena pointer aliases refuse lifetime credit" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Query = struct {
        \\    scratch: *std.heap.ArenaAllocator,
        \\    fn collect(self: *Query) ![]const u8 {
        \\        var windows: std.ArrayList(u8) = .empty;
        \\        try windows.append(self.scratch.allocator(), 1);
        \\        const storage = self.scratch;
        \\        _ = storage.reset(.free_all);
        \\        return windows.items;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Query = struct {
        \\    scratch: *std.heap.ArenaAllocator,
        \\    fn collect(self: *Query) ![]const u8 {
        \\        var windows: std.ArrayList(u8) = .empty;
        \\        try windows.append(self.scratch.allocator(), 1);
        \\        const alias = self;
        \\        _ = alias.scratch.reset(.free_all);
        \\        return windows.items;
        \\    }
        \\};
    );
}

test "return-arraylist-items: fresh receiver arena initialization precedes the borrow" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Store = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn collect(self: *Store) ![]const u8 {
        \\        self.* = .{ .arena = .init(std.heap.page_allocator) };
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.arena.allocator(), 1);
        \\        return out.items;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Store = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn collect(self: *Store) ![]const u8 {
        \\        self.* = .{ .arena = .init(std.heap.page_allocator) };
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.arena.allocator(), 1);
        \\        self.* = .{ .arena = .init(std.heap.page_allocator) };
        \\        return out.items;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Store = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn collect(self: *Store, copied: std.heap.ArenaAllocator) ![]const u8 {
        \\        self.* = .{ .arena = copied };
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.arena.allocator(), 1);
        \\        return out.items;
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Query = struct {
        \\    scratch: *std.heap.ArenaAllocator,
        \\    fn collect(self: *Query) ![]const u8 {
        \\        var storage: std.heap.ArenaAllocator = .init(std.heap.page_allocator);
        \\        defer storage.deinit();
        \\        self.* = .{ .scratch = &storage };
        \\        var out: std.ArrayList(u8) = .empty;
        \\        try out.append(self.scratch.allocator(), 1);
        \\        return out.items;
        \\    }
        \\};
    );
}
