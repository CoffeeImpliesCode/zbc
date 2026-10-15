//! The bounded loop-fact prover of the numeric oracle.
//!
//! A loop can establish a fact about its own induction variable without any
//! guard saying so: `while (i < n) { ... i += 1; }` proves `i <= n` on every
//! entry, and a rule that reports a wraparound inside that body is reporting
//! nothing. This module proves body invariants and bounded counter exit facts:
//!
//!   * which scalars the loop body assigns to values the walk already knows
//!     (`collectLoopCandidates`);
//!   * which names the loop CONDITION reads that the loop cannot change
//!     (`collectStableBoundaryReads`) — the envelope the induction is checked
//!     against;
//!   * whether those facts survive one pass of the body
//!     (`verifyLoopInvariant`);
//!   * which local counters increment at most once per bounded `for` iteration
//!     (`numericForExitFacts`).
//!
//! The state and the walk live in `value_range.zig` and are used here as the
//! ONE representation of a walk: this module owns the induction, and adding a
//! loop fact is a change here rather than a change to the statement walk, the
//! escape model or the numeric evaluator.

const std = @import("std");
const Ast = std.zig.Ast;

const numeric_nodes = @import("../model/numeric_nodes.zig");
const numeric_eval = @import("numeric_eval.zig");
const value_range = @import("value_range.zig");

const Oracle = value_range.Oracle;
const State = value_range.State;

pub const LoopKind = enum { while_, for_ };

/// How many stable boundary reads one loop's envelope may absorb.  A
/// condition with more names than this contributes the ones it has, which
/// costs a proof and never takes a wrong one.
const loop_boundary_cap: usize = 8;

pub fn numericLoopInvariants(o: *Oracle, loop_node: Ast.Node.Index, st: *const State) value_range.QueryError!std.ArrayList(numeric_eval.Fact) {
    var facts: std.ArrayList(numeric_eval.Fact) = .empty;
    errdefer facts.deinit(o.gpa);
    if (o.query != .numeric_range or !o.tokenInNode(loop_node)) return facts;
    const loop = o.tree.fullWhile(loop_node) orelse return facts;
    if (!o.tokenInNode(loop.ast.then_expr)) return facts;
    if (!value_range.pureIntegerExpression(o, loop.ast.cond_expr, 0)) return facts;
    if (!try collectLoopCandidates(o, loop_node, st, &facts) or facts.items.len == 0) {
        facts.clearRetainingCapacity();
        return facts;
    }
    // The envelope a candidate is verified against has to hold every value the
    // body can reach, and the loop's own bound is the conjunction of its
    // condition and everything the body writes.  A bound written BEFORE the
    // loop is part of that conjunction and is not in `facts` at all, which is
    // what made `while (a + 1 < b)` verify against a bound nothing in the body
    // connects to `b`: the back edge computed `a = 2`, rejected the candidate it
    // had just been handed, and dropped a bound the body does preserve.
    var envelope_facts: std.ArrayList(numeric_eval.Fact) = .empty;
    defer envelope_facts.deinit(o.gpa);
    try envelope_facts.appendSlice(o.gpa, facts.items);
    try collectStableBoundaryReads(o, loop_node, loop, st, facts.items, &envelope_facts);
    var envelope = envelope_facts.items[0].value;
    for (envelope_facts.items[1..]) |fact| envelope = envelope.join(fact.value);
    for (envelope_facts.items) |*fact| fact.value = envelope;
    var proved: State = .{};
    defer proved.deinit(o.gpa);
    const joint_verified = try verifyLoopInvariant(o, loop_node, loop, st, envelope_facts.items, &proved);
    var floor_state: State = .{};
    defer floor_state.deinit(o.gpa);
    var kept: usize = 0;
    for (facts.items) |fact| {
        var result = if (joint_verified) envelope else fact.value;
        const own_kept = joint_verified and loopFactsContain(&proved, &.{fact});
        if (own_kept) result = fact.value;
        // A joint envelope can fail or lose a counter's positive floor:
        // an unrelated accumulator or stable ceiling can admit zero.
        // Verify that counter independently with the same complete body
        // and backedge walk, without assuming the other candidates.
        if (!own_kept and fact.value == .integer and fact.value.integer.min > 0 and
            (!joint_verified or (result == .integer and result.integer.min < fact.value.integer.min)))
        {
            const floor = numeric_eval.Fact{
                .name = fact.name,
                .value = .{ .integer = .{
                    .min = fact.value.integer.min,
                    .max = if (joint_verified and result == .integer) result.integer.max else std.math.maxInt(i128),
                } },
            };
            if (try verifyLoopInvariant(o, loop_node, loop, st, &.{floor}, &floor_state)) {
                result = floor.value;
            } else if (!joint_verified) {
                // A descending positive recurrence can reach one even when
                // its initializer is larger. Widen only the floor, then
                // verify the entire body and backedge against that candidate.
                if (fact.value.integer.min <= 1) continue;
                const positive = numeric_eval.Fact{
                    .name = fact.name,
                    .value = .{ .integer = .{ .min = 1, .max = fact.value.integer.max } },
                };
                if (!try verifyLoopInvariant(o, loop_node, loop, st, &.{positive}, &floor_state)) continue;
                result = positive.value;
            }
        } else if (!joint_verified) continue;
        // Publish only assigned names; stable boundary reads are proof inputs.
        facts.items[kept] = .{ .name = fact.name, .value = result };
        kept += 1;
    }
    facts.shrinkRetainingCapacity(kept);
    return facts;
}

/// Prove copied integer projections across zero or arbitrarily many loop
/// iterations. The complete body transfer must preserve one joint envelope;
/// a last-iteration snapshot alone is never an exit fact.
pub fn numericProjectionExitFacts(
    o: *Oracle,
    loop_node: Ast.Node.Index,
    initial: *const State,
    facts: *std.ArrayList(numeric_eval.Fact),
) value_range.QueryError!void {
    if (o.query != .numeric_range or o.tokenInNode(loop_node)) return;
    // A scalar-only state has no projection induction to prove. Do not walk
    // the body, clone its collections, or scan its effects a second time.
    var eligible = false;
    for (initial.numeric.items) |fact| {
        if (!o.spend()) return;
        if (fact.value == .integer and std.mem.indexOfScalar(u8, fact.name, '.') != null) {
            eligible = true;
            break;
        }
    }
    if (!eligible) return;
    const tree = o.tree;
    var body: Ast.Node.Index = undefined;
    var continuation: ?Ast.Node.Index = null;
    if (tree.fullFor(loop_node)) |loop| {
        if (loop.ast.else_expr.unwrap() != null) return;
        body = loop.ast.then_expr;
    } else if (tree.fullWhile(loop_node)) |loop| {
        if (loop.ast.else_expr.unwrap() != null or
            !value_range.pureIntegerExpression(o, loop.ast.cond_expr, 0)) return;
        body = loop.ast.then_expr;
        continuation = loop.ast.cont_expr.unwrap();
    } else return;
    if (!projectionLoopBodySupported(o, body, 0)) return;
    if (continuation) |node| if (!projectionLoopBodySupported(o, node, 0)) return;
    var base = try initial.clone(o.gpa);
    defer base.deinit(o.gpa);
    value_range.dropLoopMutated(o, loop_node, &base);
    var candidates: [value_range.max_contract_bindings]numeric_eval.Fact = undefined;
    var count: usize = 0;
    for (initial.numeric.items) |fact| {
        if (!o.spend()) return;
        if (fact.value != .integer or std.mem.indexOfScalar(u8, fact.name, '.') == null) continue;
        if (std.meta.eql(base.numericValue(fact.name), fact.value)) continue;
        // Refuse the proof as a whole rather than publishing a subset of a
        // coupled state whose entry envelope cannot be represented.
        if (count == candidates.len) return;
        candidates[count] = fact;
        count += 1;
    }
    if (count == 0) return;
    const saved_token = o.use_token;
    o.use_token = std.math.maxInt(Ast.TokenIndex);
    defer o.use_token = saved_token;
    const saved_break = o.break_capture;
    o.break_capture = null;
    defer o.break_capture = saved_break;
    var widened = false;
    while (true) {
        if (!o.spend()) return;
        var state = try base.clone(o.gpa);
        defer state.deinit(o.gpa);
        for (candidates[0..count]) |fact| try state.setNumeric(o.gpa, fact.name, fact.value);
        if ((try value_range.enterLoopBody(o, loop_node, &state)).diverged) return;
        if ((try value_range.analyzeNode(o, body, &state)).diverged) return;
        if (continuation) |node| if ((try value_range.analyzeNode(o, node, &state)).diverged) return;
        var complete = true;
        for (candidates[0..count]) |*candidate| {
            const result = state.numericValue(candidate.name);
            if (result != .integer) return;
            const joined = candidate.value.join(result);
            if (std.meta.eql(joined, candidate.value)) continue;
            complete = false;
            // One hull learns a bounded call contract. If it still grows,
            // widen to the complete carrier, then verify that envelope too.
            // The final verification includes every candidate jointly.
            candidate.value = if (widened) value_range.NumericRange.integerType(128, true) else joined;
        }
        if (complete) {
            try facts.appendSlice(o.gpa, candidates[0..count]);
            return;
        }
        widened = true;
    }
}

fn projectionLoopBodySupported(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    if (depth == value_range.walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = value_range.walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    switch (o.tree.nodeTag(node)) {
        // These edges require separate backedge/exit captures. Declining the
        // whole proof keeps an unread edge from supplying a partial envelope.
        .@"break", .@"continue", .@"return", .@"defer", .@"errdefer" => return false,
        .fn_decl, .container_decl, .container_decl_trailing,
        .container_decl_two, .container_decl_two_trailing,
        .container_decl_arg, .container_decl_arg_trailing,
        => return true,
        else => {},
    }
    var children = @import("type_engine").AstIterator.init(o.tree, node);
    while (children.next(o.tree)) |child|
        if (!projectionLoopBodySupported(o, child, depth + 1)) return false;
    return true;
}

/// Exit ranges for local counters updated at most once per bounded iteration.
/// The iterable is evaluated independently of the body. One syntactic `+= 1`
/// outside nested loops can execute at most once per iteration, including when
/// an `if` skips it or a break ends the loop early.
pub fn numericForExitFacts(
    o: *Oracle,
    loop_node: Ast.Node.Index,
    st: *const State,
    evaluation: *numeric_eval.Evaluator,
    facts: *std.ArrayList(numeric_eval.Fact),
) error{OutOfMemory}!void {
    if (o.query != .numeric_range or o.tokenInNode(loop_node)) return;
    const tree = o.tree;
    const loop = tree.fullFor(loop_node) orelse return;
    if (loop.ast.else_expr.unwrap() != null) return;
    var iterations: ?i128 = null;
    for (loop.ast.inputs) |input| {
        if (forIterationUpper(o, evaluation, input)) |upper|
            iterations = if (iterations) |previous| @min(previous, upper) else upper;
    }
    const upper = iterations orelse return;
    if (!try collectLoopCandidates(o, loop_node, st, facts)) {
        facts.clearRetainingCapacity();
        return;
    }
    if (facts.items.len == 0) return;
    var written: [32]bool = @splat(false);
    var targets: [32]?Ast.Node.Index = @splat(null);
    const first = tree.firstToken(loop_node);
    const last = tree.lastToken(loop_node);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (node == loop_node or tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        if (!o.spend()) {
            facts.clearRetainingCapacity();
            return;
        }
        switch (tag) {
            // No nested repetition, shadowing, deferred effects or unknown
            // callee writes can take part in this certificate.
            .@"for",
            .for_simple,
            .@"while",
            .while_simple,
            .while_cont,
            .global_var_decl,
            .local_var_decl,
            .simple_var_decl,
            .aligned_var_decl,
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            .@"switch",
            .switch_comma,
            => {
                facts.clearRetainingCapacity();
                return;
            },
            .@"if", .if_simple => if (tree.fullIf(node).?.payload_token != null) {
                facts.clearRetainingCapacity();
                return;
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                if (!value_range.pureIntegerExpression(o, node, 0)) {
                    facts.clearRetainingCapacity();
                    return;
                }
            },
            else => {},
        }
        if (!numeric_nodes.isScalarAssignTag(tag)) continue;
        const parts = tree.nodeData(node).node_and_node;
        const root = value_range.lhsRootIdent(o, parts[0]) orelse {
            facts.clearRetainingCapacity();
            return;
        };
        for (facts.items, 0..) |*fact, candidate| {
            if (!std.mem.eql(u8, root, fact.name)) continue;
            if (written[candidate] or tag != .assign_add or tree.nodeTag(parts[0]) != .identifier or
                tree.nodeTag(parts[1]) != .number_literal or
                (std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(parts[1])), 0) catch 0) != 1)
                fact.value = .unknown;
            written[candidate] = true;
            targets[candidate] = parts[0];
        }
    }
    var kept: usize = 0;
    for (facts.items, 0..) |fact, candidate| {
        if (!written[candidate] or fact.value != .integer or fact.value.integer.min < 0) continue;
        if (!value_range.isLocalName(o, fact.name) or
            o.addressed.contains(fact.name) or o.pointer_roots.contains(fact.name)) continue;
        // A capture with the same spelling is a different binding.
        var shadowed = false;
        for (loop.payload_token..tree.firstToken(loop.ast.then_expr)) |token| {
            if (tree.tokenTag(@intCast(token)) == .identifier and
                std.mem.eql(u8, tree.tokenSlice(@intCast(token)), fact.name)) shadowed = true;
        }
        if (shadowed) continue;
        const maximum = std.math.add(i128, fact.value.integer.max, upper) catch continue;
        const declared = evaluation.typeRange(targets[candidate] orelse continue);
        if (declared != .integer or maximum > declared.integer.max or
            fact.value.integer.min < declared.integer.min) continue;
        facts.items[kept] = .{
            .name = fact.name,
            .value = .{ .integer = .{ .min = fact.value.integer.min, .max = maximum } },
        };
        kept += 1;
    }
    facts.shrinkRetainingCapacity(kept);
}

/// Range endpoints, slice endpoints, fixed arrays and existing length
/// snapshots supply independent iteration bounds. Unknown extents supply none.
fn forIterationUpper(o: *Oracle, evaluation: *numeric_eval.Evaluator, input: Ast.Node.Index) ?i128 {
    const tree = o.tree;
    if (tree.nodeTag(input) == .for_range) {
        const range = tree.nodeData(input).node_and_opt_node;
        const end = range[1].unwrap() orelse return null;
        if (!value_range.pureIntegerExpression(o, range[0], 0) or
            !value_range.pureIntegerExpression(o, end, 0)) return null;
        const lower = evaluation.evaluate(range[0]);
        const upper = evaluation.evaluate(end);
        if (lower != .integer or upper != .integer or lower.integer.min < 0) return null;
        return @max(0, std.math.sub(i128, upper.integer.max, lower.integer.min) catch return null);
    }
    const slice = tree.fullSlice(input);
    const source = if (slice) |sl| sl.ast.sliced else input;
    var bound: ?i128 = if (o.cache) |cache|
        if (cache.fixedArrayLenOf(source)) |length| @as(i128, length) else null
    else
        null;
    if (evaluation.allocatedLengthBound(source)) |snapshot| {
        if (snapshot == .integer and snapshot.integer.max >= 0)
            bound = if (bound) |previous| @min(previous, snapshot.integer.max) else snapshot.integer.max;
    }
    if (slice) |sl| {
        if (sl.ast.end.unwrap()) |end| {
            if (!value_range.pureIntegerExpression(o, end, 0)) return null;
            const extent = evaluation.evaluate(end);
            if (extent == .integer and extent.integer.max >= 0)
                bound = if (bound) |previous| @min(previous, extent.integer.max) else extent.integer.max;
        }
    }
    return bound;
}

/// Names the loop CONDITION reads as bare operands, that this loop cannot
/// change, and whose integer range the walk already knows.
///
/// Every test here is about STABILITY and not about the shape of the loop or
/// about who calls it, so no caller, callee or helper is exempt.  There are
/// four ways a name stops being stable and all four are excluded: the body
/// writes it (through any lvalue spelling — `a`, `a.x`, `*p`, `a[i]`), its
/// address escapes anywhere in the body, it holds a pointer rather than a
/// value, and it is not a name this body binds at all.  A name with no integer
/// range contributes nothing, and a body whose assignment targets cannot all be
/// named contributes nothing either.
///
/// The operands come from the NODES inside the condition rather than from its
/// tokens: `self.limit` is a `field_access` whose field token reads `limit`,
/// and a name picked up that way would be looked up under this body's own
/// `limit` local and given its value.
fn collectStableBoundaryReads(
    o: *Oracle,
    loop_node: Ast.Node.Index,
    loop: Ast.full.While,
    st: *const State,
    assigned: []const numeric_eval.Fact,
    out: *std.ArrayList(numeric_eval.Fact),
) error{OutOfMemory}!void {
    const tree = o.tree;
    const loop_first = tree.firstToken(loop_node);
    const loop_last = tree.lastToken(loop_node);
    const cond_first = tree.firstToken(loop.ast.cond_expr);
    const cond_last = tree.lastToken(loop.ast.cond_expr);
    var written: [32][]const u8 = undefined;
    var written_count: usize = 0;
    var operands: [loop_boundary_cap][]const u8 = undefined;
    var operand_count: usize = 0;
    var refuse = false;
    // ONE walk of the node table answers both questions, and it is the second
    // pass a loop costs only because the first one — `collectLoopCandidates` —
    // charges a step per node its BODY contains.  This walk is charged only for
    // the condition's own operands.
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        const first = tree.firstToken(node);
        const last = tree.lastToken(node);
        if (numeric_nodes.isScalarAssignTag(tag)) {
            if (first < loop_first or last > loop_last) continue;
            const root = value_range.lhsRootIdent(o, tree.nodeData(node).node_and_node[0]) orelse {
                refuse = true;
                break;
            };
            if (written_count == written.len) {
                refuse = true;
                break;
            }
            written[written_count] = root;
            written_count += 1;
            continue;
        }
        if (tag != .identifier) continue;
        if (first < cond_first or last > cond_last) continue;
        if (!o.spend()) return;
        if (operand_count == operands.len) continue;
        const name = value_range.identName(tree, node) orelse continue;
        var seen = false;
        // A block, because a brace-less `for` body takes a single
        // EXPRESSION and this `if` has no value to hand it.
        for (operands[0..operand_count]) |other| {
            if (std.mem.eql(u8, other, name)) seen = true;
        }
        if (seen) continue;
        operands[operand_count] = name;
        operand_count += 1;
    }
    if (refuse) return;
    for (operands[0..operand_count]) |name| {
        if (!value_range.isLocalName(o, name)) continue;
        if (o.addressed.contains(name) or o.pointer_roots.contains(name)) continue;
        var skip = false;
        // Blocks, not brace-less bodies: the `if` below has an ASSIGNMENT as
        // its body, and a brace-less `for` body has to be an expression.
        for (written[0..written_count]) |root| {
            if (std.mem.eql(u8, root, name)) skip = true;
        }
        for (assigned) |fact| {
            if (std.mem.eql(u8, fact.name, name)) skip = true;
        }
        if (skip) continue;
        const value = st.numericValue(name);
        if (value != .integer) continue;
        try out.append(o.gpa, .{ .name = name, .value = value });
    }
}

/// The scalar assignments a loop body performs on already-known values, unless
/// the body does something that makes the sweep meaningless (a `break` with a
/// label, a `continue`, a `defer`, a nested declaration, …).
///
/// This one question deliberately stays on the file's raw node array rather
/// than on the per-file numeric index.  It charges a STEP for every node its
/// loop body contains, before it decides whether that node is interesting at
/// all, and that charge is what the query's step counter and the bound its
/// diagnostic reports are made of.  Reading it from a tag-filtered index would
/// drop the uninteresting nodes from the count and the walk would quietly be
/// given a larger budget than it had — a cheaper query that is no longer the
/// same query.  The array walk happens once per loop the walk enters, not once
/// per expression, so it is not what made the walk superlinear in the first
/// place.
fn collectLoopCandidates(o: *Oracle, loop_node: Ast.Node.Index, st: *const State, facts: *std.ArrayList(numeric_eval.Fact)) error{OutOfMemory}!bool {
    const tree = o.tree;
    const first = tree.firstToken(loop_node);
    const last = tree.lastToken(loop_node);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (node == loop_node or tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        if (!o.spend()) return false;
        switch (tag) {
            .@"break" => if (tree.nodeData(node).opt_token_and_opt_node[0].unwrap() != null) return false,
            .@"continue", .@"defer", .@"errdefer", .@"catch", .@"orelse", .assign_destructure, .fn_decl, .@"asm", .asm_simple => return false,
            else => {},
        }
        if (!numeric_nodes.isScalarAssignTag(tag)) continue;
        const lhs = tree.nodeData(node).node_and_node[0];
        if (tree.nodeTag(lhs) != .identifier) continue;
        const name = tree.tokenSlice(tree.nodeMainToken(lhs));
        const value = st.numericValue(name);
        if (value != .integer) continue;
        var present = false;
        for (facts.items) |fact| {
            if (std.mem.eql(u8, fact.name, name)) present = true;
        }
        if (present) continue;
        if (facts.items.len == 32) return false;
        try facts.append(o.gpa, .{ .name = name, .value = value });
    }
    return true;
}

fn loopFactsContain(state: *const State, facts: []const numeric_eval.Fact) bool {
    for (facts) |fact| {
        const result = state.numericValue(fact.name);
        if (result != .integer or result.integer.min < fact.value.integer.min or
            result.integer.max > fact.value.integer.max) return false;
    }
    return true;
}

/// True when `facts` survive one pass of the loop, and — when it does —
/// `proved` receives the state at the next loop entry.  That state is what
/// decides how much of each envelope the body actually kept, so it is handed
/// back rather than discarded: the caller publishes the assigned names, and
/// publishing the envelope for all of them would hand downstream rules a
/// range as wide as the boundary read the induction needed.
fn verifyLoopInvariant(
    o: *Oracle,
    loop_node: Ast.Node.Index,
    loop: Ast.full.While,
    initial: *const State,
    facts: []const numeric_eval.Fact,
    proved: *State,
) value_range.QueryError!bool {
    var state = try initial.clone(o.gpa);
    defer state.deinit(o.gpa);
    const saved_token = o.use_token;
    o.use_token = std.math.maxInt(Ast.TokenIndex);
    defer o.use_token = saved_token;
    const saved_capture = o.break_capture;
    o.break_capture = null;
    defer o.break_capture = saved_capture;
    if ((try value_range.analyzeNode(o, loop.ast.cond_expr, &state)).diverged) return false;
    try value_range.applyRefine(o, &state, .{ .node = loop.ast.cond_expr, .truth = true });
    if (!loopFactsContain(&state, facts)) return false;
    value_range.dropLoopMutated(o, loop_node, &state);
    for (facts) |fact| try state.setNumeric(o.gpa, fact.name, fact.value);
    try value_range.applyRefine(o, &state, .{ .node = loop.ast.cond_expr, .truth = true });
    if ((try value_range.analyzeNode(o, loop.ast.then_expr, &state)).diverged) return false;
    if (loop.ast.cont_expr.unwrap()) |continuation| {
        if ((try value_range.analyzeNode(o, continuation, &state)).diverged) return false;
    }
    // Only a backedge that re-enters the body must preserve its invariant.
    // The condition and continuation are not covered by these body facts.
    if ((try value_range.analyzeNode(o, loop.ast.cond_expr, &state)).diverged) return false;
    try value_range.applyRefine(o, &state, .{ .node = loop.ast.cond_expr, .truth = true });
    if (o.budget == 0 or !loopFactsContain(&state, facts)) return false;
    try proved.replaceWith(o.gpa, &state);
    return true;
}

/// Verify header extents and unsigned snapshot progressions jointly against
/// every continuing backedge, through the canonical statement transfer.
/// The returned state owns only the proved length-related invariants.
pub fn lengthLoopInvariants(
    o: *Oracle,
    loop_node: Ast.Node.Index,
    initial: *const State,
) value_range.QueryError!State {
    var facts: State = .{};
    var proved = false;
    defer if (!proved) facts.deinit(o.gpa);
    var has_progression = false;
    for (initial.value_aliases.items) |alias| {
        if (alias.progression != null) {
            has_progression = true;
            break;
        }
    }
    if (initial.len_bounds.items.len == 0 and !has_progression) return .{};
    const tree = o.tree;
    var body: Ast.Node.Index = undefined;
    var continuation: ?Ast.Node.Index = null;
    if (tree.fullFor(loop_node)) |loop| {
        if (loop.ast.else_expr.unwrap() != null) return .{};
        body = loop.ast.then_expr;
    } else if (tree.fullWhile(loop_node)) |loop| {
        if (loop.ast.else_expr.unwrap() != null) return .{};
        body = loop.ast.then_expr;
        continuation = loop.ast.cont_expr.unwrap();
    } else return .{};
    var base = try initial.clone(o.gpa);
    defer base.deinit(o.gpa);
    value_range.dropLoopMutated(o, loop_node, &base);
    for (initial.len_bounds.items) |*fact| {
        if (!o.spend()) return .{};
        if (fact.value != .integer and !fact.isolated) continue;
        const range_kept = if (recordedLength(&base, fact.name)) |kept|
            std.meta.eql(kept, fact.value)
        else
            false;
        if (range_kept and (!fact.isolated or base.headerIsolated(fact.name))) continue;
        try facts.len_bounds.append(o.gpa, fact.*);
    }
    for (initial.value_aliases.items) |alias| {
        const progression = alias.progression orelse continue;
        if (!o.spend()) return .{};
        var kept = false;
        for (base.value_aliases.items) |other| {
            const other_progression = other.progression orelse continue;
            if (progression.tree == other_progression.tree and
                progression.token == other_progression.token and
                std.mem.eql(u8, alias.local, other.local) and
                std.mem.eql(u8, alias.path, other.path)) kept = true;
        }
        if (!kept) try facts.value_aliases.append(o.gpa, alias);
    }
    if (facts.len_bounds.items.len == 0 and facts.value_aliases.items.len == 0)
        return .{};
    if (!lengthLoopBodySupported(o, body, 0)) return .{};
    if (continuation) |node| if (!lengthLoopBodySupported(o, node, 0)) return .{};
    var state = try base.clone(o.gpa);
    defer state.deinit(o.gpa);
    for (facts.len_bounds.items) |*fact|
        try state.setHeaderBound(o.gpa, fact);
    try state.value_aliases.appendSlice(o.gpa, facts.value_aliases.items);
    var edges: value_range.BreakCapture = .{ .gpa = o.gpa };
    defer edges.deinit();
    var exits: value_range.BreakCapture = .{ .gpa = o.gpa };
    defer exits.deinit();
    const saved_token = o.use_token;
    o.use_token = std.math.maxInt(Ast.TokenIndex);
    defer o.use_token = saved_token;
    const saved_reachability = o.reachability_query;
    o.reachability_query = true;
    defer o.reachability_query = saved_reachability;
    const saved_edges = o.length_backedges;
    o.length_backedges = &edges;
    defer o.length_backedges = saved_edges;
    const saved_breaks = o.break_capture;
    o.break_capture = &exits;
    defer o.break_capture = saved_breaks;
    const saved_return = o.return_summary;
    o.return_summary = null;
    defer o.return_summary = saved_return;
    const saved_predicate = o.predicate_capture;
    o.predicate_capture = null;
    defer o.predicate_capture = saved_predicate;
    const saved_enum = o.enum_capture;
    o.enum_capture = null;
    defer o.enum_capture = saved_enum;
    const saved_capture = o.capture;
    o.capture = null;
    defer o.capture = saved_capture;
    var condition_exit: ?State = null;
    defer if (condition_exit) |*exit| exit.deinit(o.gpa);
    if (tree.fullWhile(loop_node)) |loop| {
        condition_exit = try state.clone(o.gpa);
        _ = try value_range.analyzeNode(o, loop.ast.cond_expr, &condition_exit.?);
    }
    const entry = try value_range.enterLoopBody(o, loop_node, &state);
    const flow = if (entry.diverged) entry else try value_range.analyzeNode(o, body, &state);
    if (edges.has_unresolved_target or exits.has_unresolved_target) return .{};
    if (!flow.diverged) {
        try edges.record(&state);
    }
    if (edges.state) |*backedge|
        if (continuation) |node| {
            _ = try value_range.analyzeNode(o, node, backedge);
        };
    for ([_]?*const State{
        if (edges.state) |*value| value else null,
        if (exits.state) |*value| value else null,
        if (condition_exit) |*value| value else null,
    }) |candidate_state| {
        const backedge = candidate_state orelse continue;
        for (facts.len_bounds.items) |*fact| {
            if (!o.spend()) return .{};
            if (fact.value == .integer) {
                const result = recordedLength(backedge, fact.name) orelse return .{};
                if (result != .integer or result.integer.min < fact.value.integer.min or
                    result.integer.max > fact.value.integer.max) return .{};
            }
            if (fact.isolated and !backedge.headerIsolated(fact.name)) return .{};
        }
        for (facts.value_aliases.items) |alias| {
            if (!o.spend()) return .{};
            const progression = alias.progression.?;
            var preserved = false;
            for (backedge.value_aliases.items) |other| {
                const other_progression = other.progression orelse continue;
                if (progression.tree == other_progression.tree and
                    progression.token == other_progression.token and
                    other_progression.minimum >= progression.minimum and
                    std.mem.eql(u8, alias.local, other.local) and
                    std.mem.eql(u8, alias.path, other.path)) preserved = true;
            }
            if (!preserved) return .{};
        }
    }
    proved = true;
    return facts;
}

fn recordedLength(state: *const State, name: []const u8) ?value_range.NumericRange {
    for (state.len_bounds.items) |fact|
        if (std.mem.eql(u8, fact.name, name)) return fact.value;
    return null;
}

fn lengthLoopBodySupported(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    if (depth >= value_range.walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = value_range.walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    switch (o.tree.nodeTag(node)) {
        .@"defer", .@"errdefer", .@"comptime" => return false,
        .@"break", .@"continue" => {
            if (o.tree.nodeData(node).opt_token_and_opt_node[0].unwrap() != null) return false;
        },
        .fn_decl, .container_decl, .container_decl_trailing,
        .container_decl_two, .container_decl_two_trailing,
        .container_decl_arg, .container_decl_arg_trailing,
        => return true,
        else => {},
    }
    var children = @import("type_engine").AstIterator.init(o.tree, node);
    while (children.next(o.tree)) |child|
        if (!lengthLoopBodySupported(o, child, depth + 1)) return false;
    return true;
}

test "numeric review scalar only projection exit skips cloning and body work" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa,
        \\fn read() void {
        \\    var count: usize = 0;
        \\    for (0..10) |_| { count += 1; count += 1; }
        \\    _ = count;
        \\}
    , .zig);
    defer tree.deinit(gpa);
    var loop_node: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .@"for" or tag == .for_simple) loop_node = @enumFromInt(index);
    }
    const loop = loop_node orelse return error.MissingLoop;
    var initial: State = .{};
    defer initial.deinit(gpa);
    try initial.setNumeric(gpa, "count", value_range.NumericRange.constant(0));
    var failing = std.testing.FailingAllocator.init(gpa, .{ .fail_index = 0 });
    var oracle: Oracle = .{
        .gpa = failing.allocator(),
        .tree = &tree,
        .body = .root,
        .query = .numeric_range,
        .target = "",
        .use_token = std.math.maxInt(Ast.TokenIndex),
        .budget = 2,
    };
    defer oracle.deinit();
    var facts: std.ArrayList(numeric_eval.Fact) = .empty;
    defer facts.deinit(gpa);
    try numericProjectionExitFacts(&oracle, loop, &initial, &facts);
    try std.testing.expectEqual(@as(usize, 0), facts.items.len);
    try std.testing.expect(oracle.stopped == null);
}
