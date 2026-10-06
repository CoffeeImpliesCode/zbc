//! oven-sh/bun#28633 / #29864 class — `<this>.<field> = <RHS>;` for a
//! heap-owning field without a prior `<this>.<field>.deinit()` (or
//! `.deref()` / `<allocator>.free(<this>.<field>)`) in the same
//! scope.  Each re-assignment leaks the prior allocation.
//!
//! Detection (per fn, with Db lookups for field-type → deinit-existence):
//!   1. For each fn_decl, get its first param name (`this` / `self`)
//!      and the containing type.
//!   2. Walk the body for `<this>.<field> = <RHS>;` patterns at
//!      statement position.
//!   3. Look up `<field>`'s declared type via `Db.field_types`.  If
//!      that type has a `deinit` method in the Db, the field is
//!      heap-owning per our heuristic.
//!   4. Scan backward through the K=80 preceding tokens (~5–8
//!      statements) for any of:
//!        - `<this>.<field>.<deinit|deref|destroy|close|free>(`
//!        - `<x>.free(<this>.<field>)` / `.destroy(<this>.<field>)`
//!        - `if (<this>.<field>)` (guard implies inspection-then-cleanup)
//!      If none found, fire at the assignment site.
//!
//! Constructor allowlist: skip fns named `init` / `create` / `new` /
//! `from*` / `parse*` — those are first-time-set patterns where the
//! prior field state is the declared default and there's nothing to
//! free.

const std = @import("std");
const Ast = std.zig.Ast;

const file_model = @import("../../model/file_model.zig");
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipFnDecl = tokens.skipFnDecl;
const fnProto = tokens.fnProto;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .overwrite_without_deinit)) return;

    const model = try cache.fileModel();
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const fp = fnProto(tree, &buf, node) orelse continue;
        if (returnsType(tree, fp)) continue;
        const name_tok = fp.name_token orelse continue;
        if (isConstructorName(tree.tokenSlice(name_tok))) continue;
        const ct_ti = model.containingTypeOf(node) orelse continue;
        const this_name = tokens.firstParamName(tree, fp) orelse continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, model, ct_ti, this_name, body, problems);
    }
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    model: *const file_model.FileModel,
    ct_ti: *const file_model.TypeInfo,
    this_name: []const u8,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const ct = ct_ti.qualified_name;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t: Ast.TokenIndex = first;
    while (t + 3 < last) : (t += 1) {
        // Skip past nested fns.
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }
        // Match `<this>.<field> = …;` at statement position.
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), this_name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .equal) continue;
        // Confirm `=` is at statement depth via paren/brace tracking
        // forward to the semicolon.
        const sc = findStmtSemicolon(tags, t + 4, last) orelse continue;
        const field_name = tree.tokenSlice(t + 2);
        // Field-type lookup: must have a known type whose `deinit` is
        // declared in this file AND non-trivial.  Trivial deinit
        // bodies (`{}` or `{ _ = self; }`) are common for trait
        // uniformity (CSS value types in Bun) — overwriting such a
        // field can't leak anything.
        const field_type = model.fieldType(ct, field_name) orelse {
            t = sc;
            continue;
        };
        const inner_ti = model.findType(field_type) orelse {
            t = sc;
            continue;
        };
        if (!hasNonTrivialDeinit(tree, inner_ti)) {
            t = sc;
            continue;
        }
        // Skip optional fields with a `null` default — first write
        // initializes the field rather than overwriting an owned
        // prior value (`signal: ?*Ref = null` lazy-init pattern).
        if (model.fieldIsOptionalNullDefault(ct, field_name)) {
            t = sc;
            continue;
        }
        // Undef-sentinel skip: when ANY method on this type sets the
        // field to `undefined` (constructors, thread-entry fns, reset
        // fns, etc.), `undefined` is a valid sentinel for the field.
        // The FIRST write in another method overwrites that sentinel;
        // nothing to leak.  Gate on `priorWriteInFn` returning false
        // so subsequent writes in the same fn still fire.
        if (anyMethodSetsFieldToUndefined(tree, ct_ti, field_name) and
            !priorWriteInFn(tree, first, t, this_name, field_name))
        {
            t = sc;
            continue;
        }
        // Default-undefined skip: when the field's declared default
        // is `undefined`, the first write in any method has no
        // prior owned value.  Gated on `priorWriteInFn` so later
        // writes in the same fn still fire.  Previously this was
        // only applied inside the tagged-union branch below —
        // hoisted here so the general overwrite path also benefits.
        if (fieldDefaultIsUndefinedTi(tree, ct_ti, field_name) and
            !priorWriteInFn(tree, first, t, this_name, field_name))
        {
            t = sc;
            continue;
        }
        // Default-empty-struct-literal skip: `<field>: T = .{}` —
        // the field's declared default is the all-fields-default
        // form.  For types whose own field defaults are non-owning
        // (empty strings, null pointers, `false` flags, etc.), the
        // initial value holds no resources, so the first overwrite
        // in any method has nothing to deinit.  Gated on
        // `priorWriteInFn` so subsequent writes still fire.
        // Conservative — could miss leaks when the type's own
        // defaults ARE owning, but that's unusual in practice.
        if (model.fieldDefaultIsEmptyStructLiteral(ct, field_name) and
            !priorWriteInFn(tree, first, t, this_name, field_name))
        {
            t = sc;
            continue;
        }
        // Skip when RHS is a `null` / `undefined` sentinel write —
        // canonical "clear after draining" pattern (event-loop free
        // lists, optional resets after consumption).  The leak, if
        // any, was already produced by the drain itself; this
        // statement's job is just to mark the field empty.
        if (rhsIsNullOrUndefined(tree, t + 4, sc)) {
            t = sc;
            continue;
        }
        // Skip when the assignment is inside `<…> orelse { … }`
        // where the orelse's LHS is the same `<this>.<field>` —
        // the assignment runs only when the prior value was null,
        // so there's nothing to leak.
        if (insideOrelseGuard(tree, first, t, this_name, field_name)) {
            t = sc;
            continue;
        }
        // For optional fields (`?T`) without an explicit null default:
        // when the assignment is inside ANY orelse block AND no prior
        // real (non-null) write has occurred in this fn, the orelse
        // semantics guarantee the tested value was null — lazy-init.
        // Null-sentinel clears (`self.field = null`) are NOT counted
        // as real writes, so a clear-then-orelse-init sequence
        // still suppresses correctly.
        if (fieldTypeIsOptional(tree, ct_ti, field_name) and
            insideAnyOrelseBlock(tree, first, t) and
            !priorRealWriteInFn(tree, first, t, this_name, field_name))
        {
            t = sc;
            continue;
        }
        // Skip when the assignment is inside `if (!<X>) { ... }` —
        // the negation guard means the write runs on the FALSE
        // path, i.e. when the prior state was empty/uninitialized
        // (canonical lazy-init shape).  Common for `if
        // (!this.loaded) { this.X = ... }`.
        if (insideNegationGuard(tree, first, t)) {
            t = sc;
            continue;
        }
        // Skip inline `defer <this>.<field> = saved;` and
        // `errdefer <this>.<field> = saved;` — the save/restore
        // pattern where the prior value was captured to a local and
        // the defer restores it.  Not an overwrite, no leak.
        if (insideInlineDefer(tags, t)) {
            t = sc;
            continue;
        }
        // Skip when the immediately-preceding statement is an assert
        // that mentions `<this>.<field>` — the author is asserting
        // the prior state is known/empty/default ("first set" guard,
        // common with lazy init).  K=30 tokens is enough to span an
        // `assert(condition);` statement of any reasonable shape.
        if (priorAssertOnField(tree, first, t, this_name, field_name)) {
            t = sc;
            continue;
        }
        // Save-then-deinit (imperative variant of defer-restore):
        //     var prev = this.field;
        //     this.field = new;
        //     prev.deinit();
        // The prior value was saved to a local; the cleanup happens
        // AFTER the overwrite on that local.  Scan backward for the
        // save binding, forward for `<saved>.<cleanup>(`.
        if (savedAndCleanedUp(tree, first, last, t, sc, this_name, field_name)) {
            t = sc;
            continue;
        }
        // Save-and-restore skip: the RHS of `<this>.<field> = X` is
        // a bare identifier whose source binding was
        // `<keyword> X = <this>.<field>;` earlier in the fn — the
        // statement RESTORES the saved value, it doesn't replace
        // it.  Common pattern when wiping the whole struct then
        // preserving one field:
        //   const handlers = this.handlers;
        //   this.* = undefined;
        //   this.handlers = handlers;
        if (rhsIsSavedFromSameField(tree, first, t, sc, this_name, field_name)) {
            t = sc;
            continue;
        }
        // Scan backward up to K tokens looking for prior cleanup
        // of <this>.<field>.
        if (priorCleanupExists(tree, first, t, this_name, field_name)) {
            t = sc;
            continue;
        }
        // Enum values have no owned payload.
        if (model.resolveFieldTypeQualifiedTi(ct_ti, field_name)) |leaf_ti| {
            if (leaf_ti.kind == .enum_) {
                t = sc;
                continue;
            }
        }
        // Tagged-union variant analysis: if the field's type is
        // `union(<Tag>)` AND the RHS is `.{ .<tag> = ... }` or
        // `.<tag>` AND we can reason about the PRIOR variant
        // (either the field's declared default OR a chronologically-
        // prior assignment in this fn scope), AND that prior
        // variant carries no owned payload, the retag doesn't
        // leak — there was nothing to deinit.
        //
        const union_ti = model.resolveFieldTypeQualifiedTi(ct_ti, field_name);
        if (union_ti) |un| {
            if (un.kind == .union_) {
            if (taggedUnionRetagIsSafeTi(tree, model, un,
                first, t, sc, this_name, field_name, ct)) {
                t = sc;
                continue;
            }
            // `= undefined` default: no prior value to deinit.
            // Use ct_ti directly to avoid the name-keyed findType
            // collision (Writable.Pending vs Result.Pending both
            // named "Pending").
            if (fieldDefaultIsUndefinedTi(tree, ct_ti, field_name) and
                !priorWriteInFn(tree, first, t, this_name, field_name))
            {
                t = sc;
                continue;
            }
            // Switch-arm awareness: when the assignment sits in
            // an arm of `switch (<this>.<field>) { ... }`, the
            // prior variant is constrained by the arm pattern.
            //  - `.X =>` arm: prior IS `.X` (just matched).
            //  - `else =>` arm: prior is in the COMPLEMENT of the
            //    explicit arms.
            // If every constrained-prior variant is non-owned,
            // the retag doesn't leak.
            if (switchArmRetagIsSafeTi(tree, model, un, first, t,
                this_name, field_name)) {
                t = sc;
                continue;
            }
            }
        }
        try report(gpa, problems, tree, t, this_name, field_name, ct);
        t = sc;
    }
}

/// Switch-arm awareness for tagged-union retag safety.  When the
/// assignment sits inside a `switch (<this>.<field>) { ... }`,
/// the prior variant is constrained by which arm the assignment
/// sits in:
///   - `.<X> =>` arm: prior variant IS `.X`.
///   - `else =>` arm: prior is in the complement of the explicit
///     arms.
/// Returns true iff every possible prior variant (per the arm's
/// constraint) is non-owned — the retag can't leak.
fn switchArmRetagIsSafeTi(
    tree: *const Ast,
    model: *const file_model.FileModel,
    union_ti: *const file_model.TypeInfo,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const arm = findEnclosingSwitchArm(tree, body_first, assign_tok, this_name, field_name) orelse return false;
    switch (arm) {
        .specific_tag => |tag| {
            return (model.unionVariantIsOwnedTi(union_ti, tag) orelse true) == false;
        },
        .else_arm => |explicit_tags| {
            return allVariantsExceptAreNonOwnedTi(model, union_ti, explicit_tags);
        },
    }
}

const SwitchArm = union(enum) {
    specific_tag: []const u8,
    else_arm: [16][]const u8,
};

/// Walk back from `assign_tok` looking for an enclosing
/// `switch (<this>.<field>) { ... }`.  When found, identify
/// which arm contains the assignment and return its pattern:
/// specific tag name or `else` (with the list of OTHER arm's
/// explicit tags).
fn findEnclosingSwitchArm(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) ?SwitchArm {
    const tags = tree.tokens.items(.tag);
    // Walk back finding the immediate enclosing `{` then check if
    // it's the body of an arm `=> { ... }` whose switch matches.
    var depth: i32 = 0;
    var t: Ast.TokenIndex = assign_tok;
    while (t > body_first) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    // `{` found.  Check shape backward: `=>` then
                    // pattern then `,` (or beginning of switch body).
                    return classifySwitchArm(tree, body_first, t, this_name, field_name);
                }
                depth -= 1;
            },
            else => {},
        }
    }
    return null;
}

fn classifySwitchArm(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    arm_lbrace: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) ?SwitchArm {
    const tags = tree.tokens.items(.tag);
    if (arm_lbrace < body_first + 4) return null;
    // Walk back from `{` past optional capture `|cap|` to the
    // `=>` token.
    var t: Ast.TokenIndex = arm_lbrace;
    // Optional capture: `|<ident>|` or `|*<ident>|` — single-line.
    if (t > body_first and tags[t - 1] == .pipe) {
        // walk back to the matching `|`.
        t -= 1;
        while (t > body_first and tags[t - 1] != .pipe) : (t -= 1) {}
        if (t == 0 or tags[t - 1] != .pipe) return null;
        t -= 1;
    }
    if (t == 0 or tags[t - 1] != .equal_angle_bracket_right) return null;
    const arrow_pos = t - 1;
    // Now walk back over the pattern (one token: `.<id>` / `else`,
    // OR multiple tokens for `.X, .Y => …`).  Detect the FIRST
    // token of the pattern by walking back over `.`, ident,
    // ident-comma sequences at paren-depth 0.
    if (arrow_pos < body_first + 1) return null;
    var p: Ast.TokenIndex = arrow_pos;
    var saw_else = false;
    // Collect tag names BACKWARD until we hit a `,` (separating
    // arms), `{` (switch body open), or some other delimiter.
    var tag_names: [16][]const u8 = undefined;
    var n_tags: u32 = 0;
    while (p > body_first) {
        p -= 1;
        switch (tags[p]) {
            .keyword_else => {
                saw_else = true;
                break;
            },
            .identifier => {
                if (n_tags < tag_names.len) {
                    tag_names[n_tags] = tree.tokenSlice(p);
                    n_tags += 1;
                }
            },
            .period, .comma => {},
            .l_brace => {
                // Reached switch body open — stop.
                break;
            },
            else => break,
        }
    }
    // Find the enclosing `switch ((<this>.<field>)) { ... }`.
    // Walk back past the comma-or-brace boundary; expect `)` then
    // walk back to `(` then `switch`.
    var s: Ast.TokenIndex = p;
    var brace_depth: i32 = 0;
    while (s > body_first) {
        s -= 1;
        switch (tags[s]) {
            .r_brace => brace_depth += 1,
            .l_brace => {
                if (brace_depth == 0) break;
                brace_depth -= 1;
            },
            else => {},
        }
    }
    if (s == body_first) return null;
    // `s` is the switch-body `{`.  Walk back past `)` to `(` to
    // `switch`.
    if (s < body_first + 5) return null;
    if (tags[s - 1] != .r_paren) return null;
    var pd: i32 = 1;
    var q: Ast.TokenIndex = s - 1;
    while (q > body_first and pd > 0) {
        q -= 1;
        switch (tags[q]) {
            .r_paren => pd += 1,
            .l_paren => pd -= 1,
            else => {},
        }
    }
    if (pd != 0) return null;
    if (q == 0 or tags[q - 1] != .keyword_switch) return null;
    // The scrutinee tokens are between (q+1) and (s-2) inclusive.
    // Check they're exactly `<this_name> . <field_name>` (possibly
    // wrapped in extra parens).
    var lo: Ast.TokenIndex = q + 1;
    var hi: Ast.TokenIndex = s - 2;
    while (lo + 1 < hi and tags[lo] == .l_paren and tags[hi] == .r_paren) {
        lo += 1;
        hi -= 1;
    }
    if (lo + 2 > hi) return null;
    if (tags[lo] != .identifier) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(lo), this_name)) return null;
    if (tags[lo + 1] != .period) return null;
    if (tags[lo + 2] != .identifier) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(lo + 2), field_name)) return null;
    if (lo + 2 != hi) return null;

    // Match.  Determine which arm pattern.
    if (saw_else) {
        // `else =>`: need to walk the switch body forward to
        // collect ALL explicit-tag arms.
        var explicit: [16][]const u8 = undefined;
        var n_exp = collectSwitchExplicitTags(tree, s, &explicit);
        _ = &n_exp;
        return .{ .else_arm = explicit };
    }
    if (n_tags == 0) return null;
    // Specific-tag arm: use the FIRST collected tag (closest to
    // `=>`).  Multi-pattern arms like `.X, .Y =>` may have prior
    // = .X or .Y — handle by checking only the first; the rule's
    // fire-on-first-owned approach is sufficiently conservative.
    return .{ .specific_tag = tag_names[0] };
}

fn collectSwitchExplicitTags(
    tree: *const Ast,
    body_lbrace: Ast.TokenIndex,
    out: *[16][]const u8,
) u32 {
    const tags = tree.tokens.items(.tag);
    var n: u32 = 0;
    // Walk between `{` and matching `}` of the switch body.
    var depth: i32 = 1;
    var t: Ast.TokenIndex = body_lbrace + 1;
    while (t < tags.len and depth > 0) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => depth -= 1,
            .period => {
                if (depth == 1 and t + 1 < tags.len and tags[t + 1] == .identifier) {
                    if (n < out.len) {
                        out[n] = tree.tokenSlice(t + 1);
                        n += 1;
                    }
                }
            },
            else => {},
        }
    }
    return n;
}

fn allVariantsExceptAreNonOwnedTi(
    model: *const file_model.FileModel,
    ti: *const file_model.TypeInfo,
    explicit_tags: [16][]const u8,
) bool {
    const tree = model.tree;
    const tags = tree.tokens.items(.tag);
    var t = ti.body_first + 1;
    while (t < ti.body_last) : (t += 1) {
        if (tags[t] == .keyword_fn or tags[t] == .keyword_pub or
            tags[t] == .keyword_const or tags[t] == .keyword_var)
        {
            t = skipPastTypeDecl(tags, t, ti.body_last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        const name = tree.tokenSlice(t);
        // Is `name` in explicit_tags?  If yes, skip (it's the
        // arm-matched variant).
        var found = false;
        for (explicit_tags) |et| {
            if (et.len == 0) continue;
            if (std.mem.eql(u8, et, name)) {
                found = true;
                break;
            }
        }
        if (found) {
            // Skip past variant's payload to next.
            if (t + 1 < ti.body_last and tags[t + 1] == .colon) {
                t = skipPastVariantPayload(tags, t + 2, ti.body_last);
            }
            continue;
        }
        // Variant not in explicit set; must be non-owned.
        if (model.unionVariantIsOwnedTi(ti, name) orelse true) {
            return false;
        }
        if (t + 1 < ti.body_last and tags[t + 1] == .colon) {
            t = skipPastVariantPayload(tags, t + 2, ti.body_last);
        }
    }
    return true;
}

fn skipPastTypeDecl(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex) Ast.TokenIndex {
    var t = start;
    var brace: i32 = 0;
    var paren: i32 = 0;
    while (t < last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => brace += 1,
            .r_brace => {
                brace -= 1;
                if (brace == 0 and paren == 0) return t;
            },
            .l_paren => paren += 1,
            .r_paren => paren -= 1,
            .semicolon => if (brace == 0 and paren == 0) return t,
            else => {},
        }
    }
    return last;
}

fn skipPastVariantPayload(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex) Ast.TokenIndex {
    var t = start;
    var pd: i32 = 0;
    while (t < last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => pd += 1,
            .r_paren, .r_bracket, .r_brace => pd -= 1,
            .comma => if (pd == 0) return t,
            else => {},
        }
    }
    return last;
}


/// Tagged-union retag safety analysis.  For a `<this>.<field> =
/// .{ .<tag> = ... };` where `<field>`'s type is `union(enum)`,
/// the retag is safe iff the PRIOR variant carried no owned
/// payload.  The prior variant is determined by:
///   1. Walking BACK from the current assignment for a chronologically
///      prior `<this>.<field> = .{ .<other> = ... };` in scope.
///   2. If none found in this fn, falling back to the field's
///      declared default `.<tag>`.
/// "Owned" payload = a payload type that has a `deinit` method (or
/// equivalent); empty / primitive payloads are non-owned.
fn taggedUnionRetagIsSafeTi(
    tree: *const Ast,
    model: *const file_model.FileModel,
    union_ti: *const file_model.TypeInfo,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    sc: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
    outer_type_name: []const u8,
) bool {
    _ = sc;
    if (priorVariantInFn(tree, body_first, assign_tok, this_name, field_name)) |prior_tag| {
        return (model.unionVariantIsOwnedTi(union_ti, prior_tag) orelse true) == false;
    }
    // No prior assignment in this fn.  Check the field's declared
    // default tag first.  Then fall back to scanning the type's
    // init method, then to `= undefined` (a non-owned sentinel —
    // there's no prior value to deinit).
    if (model.fieldDefaultUnionTag(outer_type_name, field_name)) |dt|
        return (model.unionVariantIsOwnedTi(union_ti, dt) orelse true) == false;
    if (initFnDefaultUnionTag(tree, model, outer_type_name, field_name)) |dt|
        return (model.unionVariantIsOwnedTi(union_ti, dt) orelse true) == false;
    return false;
}

/// True iff the field's declared default value is the literal
/// `undefined`.  Used by the union retag check: an `undefined`
/// default has no prior value to deinit on first write.
fn fieldDefaultIsUndefinedTi(
    tree: *const Ast,
    ti: *const file_model.TypeInfo,
    field_name: []const u8,
) bool {
    const f = ti.findField(field_name) orelse return false;
    if (!f.has_default) return false;
    const tags = tree.tokens.items(.tag);
    if (f.type_last + 1 >= tags.len) return false;
    var eq: Ast.TokenIndex = f.type_last + 1;
    while (eq < tags.len and tags[eq] != .equal) : (eq += 1) {}
    if (eq >= tags.len) return false;
    if (eq + 1 >= tags.len) return false;
    if (tags[eq + 1] != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(eq + 1), "undefined");
}

/// True iff the fn body contains a prior write to `<this>.<field>`
/// before `assign_tok`.  Used to gate the undefined-default skip:
/// only skip on the FIRST write in this fn.
fn priorWriteInFn(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (assign_tok < body_first + 4) return false;
    var t: Ast.TokenIndex = body_first;
    while (t + 4 <= assign_tok - 1) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), this_name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field_name)) continue;
        if (tags[t + 3] != .equal) continue;
        return true;
    }
    return false;
}

/// Fallback: when the field has no inline default `= .<tag>`,
/// scan the containing type's `init` method body for the first
/// `.<field> = .<tag>` (in a struct-init literal) or
/// `<recv>.<field> = .<tag>` (imperative).  Returns the tag name
/// when found.  Common in Bun's codebase where init() sets the
/// initial union variant explicitly rather than declaring a
/// field default.
fn initFnDefaultUnionTag(
    tree: *const Ast,
    model: *const file_model.FileModel,
    outer_type_name: []const u8,
    field_name: []const u8,
) ?[]const u8 {
    const ti = model.findType(outer_type_name) orelse return null;
    const init_method = ti.findMethod("init") orelse return null;
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = init_method.body_first;
    const last = init_method.body_last;
    while (t + 4 <= last) : (t += 1) {
        // Struct-init form: `. <field> = . <tag>`.
        if (tags[t] == .period and
            tags[t + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 1), field_name) and
            tags[t + 2] == .equal and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier)
        {
            return tree.tokenSlice(t + 4);
        }
        // Imperative form: `<recv> . <field> = . <tag>` — needs
        // one more token before the period.
        if (t > 0 and tags[t - 1] == .identifier and
            tags[t] == .period and
            tags[t + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 1), field_name) and
            tags[t + 2] == .equal and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier)
        {
            return tree.tokenSlice(t + 4);
        }
    }
    return null;
}

/// True iff any of the type's constructor methods (`init` / `create`
/// / `new` / `from*`) sets `<field>` to the literal `undefined` in
/// its body — typically inside the returned struct literal:
///   `return Self{ ..., .<field> = undefined, ... };`
/// or imperatively `<self>.<field> = undefined;`.  In either case
/// True iff ANY method on the type sets `.<field> = undefined` or
/// `<recv>.<field> = undefined`.  Name-agnostic: constructors, thread-
/// entry fns, reset helpers, etc. all count.  When this is true,
/// `undefined` is a documented sentinel for the field — the FIRST
/// overwrite in another method has no prior owned value to deinit.
/// Subsequent writes WOULD leak — gate the skip on `priorWriteInFn`.
fn anyMethodSetsFieldToUndefined(
    tree: *const Ast,
    ti: *const file_model.TypeInfo,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    for (ti.methods) |m| {
        var t: Ast.TokenIndex = m.body_first;
        const last = m.body_last;
        while (t + 4 <= last) : (t += 1) {
            // `.<field> = undefined`
            if (tags[t] == .period and
                tags[t + 1] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t + 1), field_name) and
                tags[t + 2] == .equal and
                tags[t + 3] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t + 3), "undefined"))
            {
                return true;
            }
            // `<recv>.<field> = undefined`
            if (t > 0 and tags[t - 1] == .identifier and
                tags[t] == .period and
                tags[t + 1] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t + 1), field_name) and
                tags[t + 2] == .equal and
                tags[t + 3] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t + 3), "undefined"))
            {
                return true;
            }
        }
    }
    return false;
}

/// Walk backward from `assign_tok` to `body_first` looking for the
/// most-recent prior assignment `<this>.<field> = .{ .<tag> = ... };`.
/// Returns the prior tag name on hit, null on miss.  Brace depth
/// is NOT tracked: any earlier write in the same fn body establishes
/// the variant that the abstract state holds when the current write
/// executes (since assignments earlier in source order dominate later
/// ones in the common straight-line case; nested-block writes are a
/// conservative overestimate of "could have run").
fn priorVariantInFn(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    if (assign_tok < body_first + 5) return null;
    var t: Ast.TokenIndex = assign_tok;
    // Track brace depth going backward: `}` enters a block (+1),
    // `{` exits a block (-1).  When depth drops below 0 we have
    // crossed the opening brace of the assignment's own enclosing
    // block — anything further back is either in the parent scope
    // or a sibling arm of a switch/if statement, neither of which
    // is guaranteed to have run before the current assignment.
    // Restricting to depth 0 means we only return unconditional
    // prior writes at the same nesting level.
    var depth: i32 = 0;
    while (t > body_first + 4) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => { depth += 1; continue; },
            .l_brace => {
                depth -= 1;
                if (depth < 0) break; // exited enclosing block — stop
                continue;
            },
            else => {},
        }
        if (depth != 0) continue; // skip writes inside nested blocks
        // Look for `<this> . <field> = . <tag>` at this position.
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), this_name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field_name)) continue;
        if (tags[t + 3] != .equal) continue;
        // Two RHS shapes for tag extraction:
        //   a) `.<tag>` — bare tag (no payload).
        //   b) `.{ .<tag> = ... }` — struct-init form.
        if (t + 5 >= tags.len) continue;
        // Shape (a): `= .<tag>` then `;` or `,`.
        if (tags[t + 4] == .period and tags[t + 5] == .identifier) {
            const after = t + 6;
            if (after < tags.len) {
                switch (tags[after]) {
                    .semicolon, .comma => return tree.tokenSlice(t + 5),
                    else => {},
                }
            }
        }
        // Shape (b): `= . { . <tag> = …`.
        if (t + 7 < tags.len and
            tags[t + 4] == .period and
            tags[t + 5] == .l_brace and
            tags[t + 6] == .period and
            tags[t + 7] == .identifier)
        {
            return tree.tokenSlice(t + 7);
        }
        // Other RHS shape (call returning union) — we can't extract
        // a literal tag from here.  Treat as "prior variant unknown"
        // by returning null so the caller falls back to default.
        return null;
    }
    return null;
}

/// True iff there's a backward `var <X> = <this>.<field>;` binding
/// BEFORE the assignment AND a forward `<X>.<cleanup>(` call AFTER
/// the assignment, both within the same enclosing block.  Catches
/// the imperative save-then-deinit pattern:
///     var prev = this.field;
///     this.field = new;
///     prev.deinit();
/// True iff the RHS of `<this>.<field> = X` at `assign_tok` is a
/// bare identifier `X` whose binding earlier in the fn was
/// `<keyword> X = <this>.<field>;` — the canonical save form for a
/// save-and-restore pattern.  Used to skip the rule on
/// `<this>.<field> = <saved-local>;` after the local was previously
/// captured from the same field.
fn rhsIsSavedFromSameField(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    sc: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    // The assignment is `<this> . <field> = <rhs> ;` — the `=` is
    // at assign_tok + 3.  RHS starts at assign_tok + 4.
    if (assign_tok + 4 >= sc) return false;
    if (tags[assign_tok + 4] != .identifier) return false;
    // RHS must be a BARE identifier (single token followed by `;`).
    if (assign_tok + 5 != sc) return false;
    const rhs_name = tree.tokenSlice(assign_tok + 4);
    // Backward scan for `<keyword_var|const> <rhs_name> = <this> . <field> ;`.
    const K: u32 = 30;
    var t: Ast.TokenIndex = assign_tok;
    var i: u32 = 0;
    while (t > body_first and i < K) : (i += 1) {
        t -= 1;
        if (tags[t] != .keyword_var and tags[t] != .keyword_const) continue;
        if (t + 5 >= assign_tok) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), rhs_name)) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), this_name)) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 5), field_name)) continue;
        return true;
    }
    return false;
}

fn savedAndCleanedUp(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    sc: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    // Backward scan for `<keyword_var|const> <X> = <this>.<field>;`
    // — bounded to K=30 tokens or the enclosing block start.
    const K: u32 = 30;
    var saved_name: ?[]const u8 = null;
    var depth: i32 = 0;
    var i: u32 = 0;
    var t: Ast.TokenIndex = assign_tok;
    while (t > body_first and i < K) : (i += 1) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) break;
                depth -= 1;
            },
            else => {},
        }
        if (depth != 0) continue;
        // Match `keyword_var <ident> = <this_name> . <field_name>`.
        if (tags[t] != .keyword_var and tags[t] != .keyword_const) continue;
        if (t + 5 > body_last) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), this_name)) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 5), field_name)) continue;
        saved_name = tree.tokenSlice(t + 1);
        break;
    }
    const name = saved_name orelse return false;
    // Forward scan from after the `;` for `<name>.<cleanup>(`.
    var k: Ast.TokenIndex = sc + 1;
    depth = 0;
    i = 0;
    while (k <= body_last and i < K) : ({
        k += 1;
        i += 1;
    }) {
        switch (tags[k]) {
            .l_brace => depth += 1,
            .r_brace => {
                if (depth == 0) return false;
                depth -= 1;
            },
            else => {},
        }
        if (depth != 0) continue;
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), name)) continue;
        if (k + 3 > body_last) continue;
        if (tags[k + 1] != .period) continue;
        if (tags[k + 2] != .identifier) continue;
        if (tags[k + 3] != .l_paren) continue;
        const m = tree.tokenSlice(k + 2);
        if (std.mem.eql(u8, m, "deinit") or std.mem.eql(u8, m, "deref") or
            std.mem.eql(u8, m, "destroy") or std.mem.eql(u8, m, "close") or
            std.mem.eql(u8, m, "free") or std.mem.eql(u8, m, "finalize") or
            std.mem.eql(u8, m, "dispose"))
        {
            return true;
        }
    }
    return false;
}

/// True iff `ti` has a `deinit` method with a non-trivial body —
/// any statement that's not a `_ = <expr>;` discard.  Mirrors the
/// same check in owned-field-no-outer-cleanup.  Returns false for
/// types whose deinit is `{}` or only discards (CSS uniform-API
/// conformance); overwriting such a field can't leak anything.
fn hasNonTrivialDeinit(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    for (ti.methods) |m| {
        if (!std.mem.eql(u8, m.name, "deinit")) continue;
        if (!isTrivialBody(tree, m.body_first, m.body_last)) return true;
    }
    return false;
}

const isTrivialBody = tokens.isTrivialBody;

/// True iff `assign_tok` (the `<this>` ident in `<this>.<field> = …`)
/// is the body of an inline `defer` / `errdefer` statement.  Matches:
///   `defer <this>.<field> = saved;`
///   `errdefer <this>.<field> = saved;`
///   `errdefer |err| <this>.<field> = saved;`
///   `defer { <this>.<field> = saved; ... }` (first stmt in block)
fn insideInlineDefer(tags: []const std.zig.Token.Tag, assign_tok: Ast.TokenIndex) bool {
    if (assign_tok == 0) return false;
    const t = assign_tok - 1;
    // Bare `defer` / `errdefer` immediately before.
    if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) return true;
    // `errdefer |err|` — peel `|err|`.
    if (tags[t] == .pipe and t >= 3) {
        if (tags[t - 1] == .identifier and tags[t - 2] == .pipe) {
            if (t >= 4 and tags[t - 3] == .keyword_errdefer) return true;
        }
    }
    // Block form: `defer { <stmt>; … }` — first stmt has `{` then
    // `defer`/`errdefer` directly before it.
    if (tags[t] == .l_brace and t >= 1) {
        if (tags[t - 1] == .keyword_defer or tags[t - 1] == .keyword_errdefer) return true;
    }
    return false;
}

/// True iff a recent `assert(<expr involving this.field>)` /
/// `bun.assert(...)` / `std.debug.assert(...)` precedes `assign_tok`.
/// Bounded to a 30-token lookback so we don't pick up unrelated
/// asserts earlier in the fn.
fn priorAssertOnField(
    tree: *const Ast,
    start: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    const K: u32 = 64;
    var i: u32 = 0;
    var t: Ast.TokenIndex = assign_tok;
    var saw_field = false;
    while (t > start and i < K) : (i += 1) {
        t -= 1;
        if (tags[t] == .identifier) {
            const s = tree.tokenSlice(t);
            // Look for the field-name ident followed (going forward)
            // by the this name — i.e. `<this>.<field>` shape.
            if (std.mem.eql(u8, s, field_name) and t >= 2 and
                tags[t - 1] == .period and tags[t - 2] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t - 2), this_name))
            {
                saw_field = true;
            }
            // The assert identifier.  Recognize `assert` and the
            // last-segment of `bun.assert` / `std.debug.assert` etc.
            if (saw_field and std.mem.eql(u8, s, "assert")) return true;
        }
    }
    return false;
}

/// True iff the RHS at `[start, end)` is exactly `null`, `undefined`,
/// or `.{}` / `&.{}` / `.empty` — the canonical "clear" sentinels.
fn rhsIsNullOrUndefined(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (start >= end) return false;
    // Single-token forms.
    if (start + 1 == end) {
        if (tags[start] != .identifier) return false;
        const s = tree.tokenSlice(start);
        return std.mem.eql(u8, s, "null") or std.mem.eql(u8, s, "undefined");
    }
    // `.{}` / `&.{}` / `.empty`.
    if (start + 3 == end and
        tags[start] == .period and
        tags[start + 1] == .l_brace and
        tags[start + 2] == .r_brace) return true;
    if (start + 4 == end and
        tags[start] == .ampersand and
        tags[start + 1] == .period and
        tags[start + 2] == .l_brace and
        tags[start + 3] == .r_brace) return true;
    if (start + 2 == end and
        tags[start] == .period and
        tags[start + 1] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(start + 1), "empty")) return true;
    return false;
}

/// True iff the assignment at `assign_tok` is inside an
/// `<this>.<field> orelse { … }` block — i.e. the enclosing `{`
/// is preceded by `keyword_orelse`, and the immediately-preceding
/// tokens before that `orelse` are the same `<this>.<field>` chain.
/// Inside such a block the prior value is guaranteed null, so the
/// assignment isn't an overwrite.
/// True iff the assignment sits inside `if (!<expr>) { ... }` —
/// the negation-guarded init pattern.  Walk back to the enclosing
/// `{`, check that the matching token sequence reading back is
/// `(` ... `!` ... `)` ... `{`.  Conservative: only the very
/// outermost expression's first non-paren token after the `(` is
/// inspected; nested `!` isn't required.
fn insideNegationGuard(
    tree: *const Ast,
    start: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    var depth: i32 = 0;
    var t: Ast.TokenIndex = assign_tok;
    while (t > start) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    // Found the opening brace of our enclosing block.
                    // Must be preceded by `)` (the if-condition's close).
                    if (t < 3) return false;
                    if (tags[t - 1] != .r_paren) return false;
                    // Walk back paren-balanced to the `(`.
                    var p_depth: i32 = 1;
                    var p: Ast.TokenIndex = t - 1;
                    while (p > start and p_depth > 0) {
                        p -= 1;
                        switch (tags[p]) {
                            .r_paren => p_depth += 1,
                            .l_paren => p_depth -= 1,
                            else => {},
                        }
                    }
                    if (p_depth != 0) return false;
                    // Token before `(` should be `if`.
                    if (p == 0 or tags[p - 1] != .keyword_if) return false;
                    // First token inside `(` must be `!`.
                    if (p + 1 >= t - 1) return false;
                    return tags[p + 1] == .bang;
                }
                depth -= 1;
            },
            else => {},
        }
    }
    return false;
}

fn insideOrelseGuard(
    tree: *const Ast,
    start: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    // Walk back finding the matching `{` for our enclosing block,
    // tracking brace depth.
    var depth: i32 = 0;
    var t: Ast.TokenIndex = assign_tok;
    while (t > start) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    // Found the opening brace.  Check what precedes it.
                    if (t < 3) return false;
                    if (tags[t - 1] != .keyword_orelse) return false;
                    // Token at t-2 should be the field ident, t-3
                    // the period, t-4 the this ident.
                    if (t < 4) return false;
                    if (tags[t - 2] != .identifier or
                        !std.mem.eql(u8, tree.tokenSlice(t - 2), field_name)) return false;
                    if (tags[t - 3] != .period) return false;
                    if (tags[t - 4] != .identifier or
                        !std.mem.eql(u8, tree.tokenSlice(t - 4), this_name)) return false;
                    return true;
                }
                depth -= 1;
            },
            else => {},
        }
    }
    return false;
}

/// Walk tokens backward from `assign_tok` (the `<this>` ident) up
/// to `start` (body's firstToken) or 80 tokens — whichever is closer
/// — looking for prior cleanup of `<this>.<field>`.  Accepts:
///   - `<this>.<field>.deinit(` / `.deref(` / `.destroy(` / `.close(` / `.free(` / `.finalize(`
///   - `<x>.free(<this>.<field>)` / `.destroy(<this>.<field>)`
///   - `if (<this>.<field>) |…|` (guard implies cleanup-on-some-path)
fn priorCleanupExists(
    tree: *const Ast,
    start: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    const win_size: u32 = 80;
    var window_start: Ast.TokenIndex = start;
    if (assign_tok > start + win_size) window_start = assign_tok - win_size;
    var t: Ast.TokenIndex = window_start;
    while (t + 3 < assign_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), this_name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field_name)) continue;
        // Pattern A: `<this>.<field>.<cleanup>(`.
        if (t + 4 < assign_tok and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            isCleanupMethodName(tree.tokenSlice(t + 4)))
        {
            return true;
        }
        // Pattern B: `if (<this>.<field>)` guard.
        if (t >= 2 and tags[t - 1] == .l_paren and tags[t - 2] == .keyword_if) {
            return true;
        }
        // Pattern C: `<x>.<free/destroy>(<this>.<field>)`.
        // Token before the start of `<this>.<field>` would be `l_paren`,
        // preceded by `.free` / `.destroy`.
        if (t >= 3 and tags[t - 1] == .l_paren and
            tags[t - 2] == .identifier)
        {
            const callee = tree.tokenSlice(t - 2);
            if (isFreeOrDestroy(callee)) return true;
        }
    }
    return false;
}

const isCleanupMethodName = method_names.isCleanupMethodName;

fn isFreeOrDestroy(name: []const u8) bool {
    return std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "destroy");
}

fn isConstructorName(name: []const u8) bool {
    if (std.mem.eql(u8, name, "init")) return true;
    if (std.mem.eql(u8, name, "create")) return true;
    if (std.mem.eql(u8, name, "new")) return true;
    if (std.mem.eql(u8, name, "setup")) return true;
    if (std.mem.eql(u8, name, "configure")) return true;
    if (std.mem.startsWith(u8, name, "init")) return true;
    if (std.mem.startsWith(u8, name, "from")) return true;
    if (std.mem.startsWith(u8, name, "parse")) return true;
    if (std.mem.startsWith(u8, name, "decode")) return true;
    return false;
}

fn returnsType(tree: *const Ast, fp: Ast.full.FnProto) bool {
    const rt = fp.ast.return_type.unwrap() orelse return false;
    const first = tree.firstToken(rt);
    const last = tree.lastToken(rt);
    if (first != last) return false;
    return tree.tokens.items(.tag)[first] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(first), "type");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    this_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
    ct: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}` is overwritten here without first calling `{s}.{s}.deinit()` (or `.deref()` / `<allocator>.free(...)`); the prior value of `{s}.{s}` (which is `{s}.{s}` — a type with a `deinit` method) leaks every time this assignment runs",
        .{ this_name, field_name, this_name, field_name, this_name, field_name, ct, field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "overwrite-without-deinit",
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, this_tok),
        .end = Pos.fromTokenEnd(tree, this_tok + 2),
        .message = msg,
    });
}

/// Like `priorWriteInFn` but excludes writes where the RHS is a bare
/// `null` or `undefined` token — those are sentinel-clears, not real
/// value assignments.  Used so that `self.field = null; … orelse { self.field = v; }`
/// is still recognised as lazy-init.
fn priorRealWriteInFn(
    tree: *const Ast,
    body_first: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
    this_name: []const u8,
    field_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (assign_tok < body_first + 4) return false;
    var t: Ast.TokenIndex = body_first;
    while (t + 4 <= assign_tok - 1) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), this_name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field_name)) continue;
        if (tags[t + 3] != .equal) continue;
        // RHS: skip if bare `null` or `undefined`.
        const rhs = t + 4;
        if (rhs < assign_tok and tags[rhs] == .identifier) {
            const s = tree.tokenSlice(rhs);
            if (std.mem.eql(u8, s, "null") or std.mem.eql(u8, s, "undefined")) continue;
        }
        return true;
    }
    return false;
}

/// True when the field's declared type begins with `?` — i.e. it is
/// an optional type regardless of whether it has an explicit null default.
fn fieldTypeIsOptional(
    tree: *const Ast,
    ct_ti: *const file_model.TypeInfo,
    field_name: []const u8,
) bool {
    const f = ct_ti.findField(field_name) orelse return false;
    return tree.tokens.items(.tag)[f.type_first] == .question_mark;
}

/// True when `assign_tok` is directly enclosed by the body of an
/// `orelse { … }` block — regardless of what expression precedes
/// the `orelse`.  Walks backward tracking brace depth; the first
/// depth-0 `{` that is immediately preceded by `orelse` returns true.
fn insideAnyOrelseBlock(
    tree: *const Ast,
    start: Ast.TokenIndex,
    assign_tok: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    var depth: i32 = 0;
    var t: Ast.TokenIndex = assign_tok;
    while (t > start) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    if (t < 1) return false;
                    return tags[t - 1] == .keyword_orelse;
                }
                depth -= 1;
            },
            else => {},
        }
    }
    return false;
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "overwrite-without-deinit: reassign deinit-able field without prior cleanup fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Owned = struct {
        \\    buf: []u8,
        \\    pub fn deinit(self: *Owned) void { self.buf.len = 0; }
        \\};
        \\const NameOrIndex = union(enum) {
        \\    name: Owned,
        \\    index: u32,
        \\    duplicate,
        \\    pub fn deinit(self: *NameOrIndex) void { _ = self; self.* = .duplicate; }
        \\};
        \\const Field = struct {
        \\    name_or_index: NameOrIndex = .name,
        \\    pub fn markDup(this: *Field) void {
        \\        this.name_or_index = .duplicate;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("overwrite-without-deinit", problems.items[0].rule_id);
}

test "overwrite-without-deinit: prior `.deinit()` is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const NameOrIndex = union(enum) {
        \\    name: u32,
        \\    duplicate,
        \\    pub fn deinit(self: *NameOrIndex) void { _ = self; self.* = .duplicate; }
        \\};
        \\const Field = struct {
        \\    name_or_index: NameOrIndex = .duplicate,
        \\    pub fn markDup(this: *Field) void {
        \\        this.name_or_index.deinit();
        \\        this.name_or_index = .duplicate;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: field type has no `deinit` method — skip" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Plain = struct { a: u32 = 0 };
        \\const Owner = struct {
        \\    inner: Plain = .{},
        \\    pub fn set(this: *Owner, p: Plain) void {
        \\        this.inner = p;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: constructor fn (init/create/from*) is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const NameOrIndex = union(enum) {
        \\    name: u32,
        \\    duplicate,
        \\    pub fn deinit(self: *NameOrIndex) void { _ = self; self.* = .duplicate; }
        \\};
        \\const Field = struct {
        \\    name_or_index: NameOrIndex = .duplicate,
        \\    pub fn init(this: *Field) void {
        \\        this.name_or_index = .duplicate;
        \\    }
        \\    pub fn fromJS(this: *Field) void {
        \\        this.name_or_index = .duplicate;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: explicit `<allocator>.free(this.field)` cleanup is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Inner = struct { pub fn deinit(self: *Inner) void { self.* = undefined; } };
        \\const Owner = struct {
        \\    inner: Inner = .{},
        \\    pub fn replace(this: *Owner, new_inner: Inner, a: std.mem.Allocator) void {
        \\        a.destroy(this.inner);
        \\        this.inner = new_inner;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: `if (this.field) |…|` guard counts as cleanup" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Inner = struct { pub fn deinit(self: *Inner) void { self.* = undefined; } };
        \\const Owner = struct {
        \\    inner: ?Inner = null,
        \\    pub fn swap(this: *Owner, new_inner: Inner) void {
        \\        if (this.inner) |*old| old.deinit();
        \\        this.inner = new_inner;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: inline `defer this.field = saved;` (save/restore) doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Inner = struct { pub fn deinit(self: *Inner) void { self.* = undefined; } };
        \\const Owner = struct {
        \\    inner: Inner,
        \\    pub fn withTemp(this: *Owner, new_inner: Inner) void {
        \\        const prev = this.inner;
        \\        defer this.inner = prev;
        \\        this.inner = new_inner;
        \\        _ = new_inner;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // The `defer this.inner = prev;` line is a restore — no FP there.
    // The unguarded `this.inner = new_inner` IS a real overwrite
    // without prior cleanup → should fire exactly once.
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "overwrite-without-deinit: sibling switch arms are mutually exclusive — no FP" {
    // Mimics the HTMLBundle.zig:433 pattern: a completion callback
    // that transitions `this.state` from `.building` in one arm to
    // `.done` in another arm of `switch (result)`.  The two arms are
    // mutually exclusive so `priorVariantInFn` must NOT pick up the
    // assignment in the `.err` arm as the "prior state" for the
    // `.ok` arm — that would produce a false positive.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Task = struct { pub fn deref(_: *Task) void {} };
        \\const State = union(enum) {
        \\    pending,
        \\    building: ?*Task,
        \\    err: u32,
        \\    done: u32,
        \\    pub fn deinit(this: *State) void {
        \\        switch (this.*) {
        \\            .building => |t| if (t) |c| c.deref(),
        \\            else => {},
        \\        }
        \\    }
        \\};
        \\const Owner = struct {
        \\    state: State = .pending,
        \\    pub fn init(this: *Owner) void { this.state = .pending; }
        \\    pub fn onComplete(this: *Owner, result: union(enum) { ok: u32, fail: u32 }) void {
        \\        switch (result) {
        \\            .fail => |e| {
        \\                this.state = .{ .err = e };
        \\            },
        \\            .ok => |v| {
        \\                this.state = .{ .done = v };
        \\            },
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: assert(this.field == default) gates the write — no fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Inner = struct { pub fn deinit(self: *Inner) void { self.* = undefined; } };
        \\const Owner = struct {
        \\    inner: Inner,
        \\    pub fn lazyInit(this: *Owner, new_inner: Inner) void {
        \\        bun.assert(this.inner == .empty);
        \\        this.inner = new_inner;
        \\    }
        \\};
        \\const bun = struct { pub fn assert(_: bool) void {} };
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: non-constructor fn sets field=undefined → first write in thread entry no fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const CfgPart = struct {
        \\    data: []u8,
        \\    pub fn deinit(self: *CfgPart, alloc: std.mem.Allocator) void { alloc.free(self.data); }
        \\};
        \\const ScopeCfgParallel = struct {
        \\    thread: std.Thread,
        \\    result: CfgPart,
        \\    err: ?anyerror,
        \\    fn entry(self: *ScopeCfgParallel) void {
        \\        self.result = compute() catch return;
        \\    }
        \\    pub fn start(allocator: std.mem.Allocator) !*ScopeCfgParallel {
        \\        const self = try allocator.create(ScopeCfgParallel);
        \\        self.* = .{ .thread = undefined, .result = undefined, .err = null };
        \\        self.thread = try std.Thread.spawn(.{}, entry, .{self});
        \\        return self;
        \\    }
        \\};
        \\fn compute() !CfgPart { return .{ .data = &[_]u8{} }; }
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "overwrite-without-deinit: struct-typed field with non-trivial deinit fires" {
    const gpa = std.testing.allocator;
    // Field has no default (`inner_real: InnerReal` — no `= .{}`), so the
    // empty-struct-literal suppression does not apply and the rule fires.
    var problems = try testing.runRule(gpa, check,
        \\const InnerReal = struct {
        \\    buf: []const u8 = &.{},
        \\    pub fn deinit(self: *InnerReal) void { self.buf = &.{}; }
        \\};
        \\const Owner = struct {
        \\    inner_real: InnerReal,
        \\    pub fn deinit(this: *Owner) void { this.inner_real.deinit(); }
        \\    pub fn set(this: *Owner, new_inner: InnerReal) void {
        \\        this.inner_real = new_inner;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "overwrite-without-deinit")) found = true;
    }
    try std.testing.expect(found);
}

test "overwrite-without-deinit: optional field first write inside orelse block — no fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Owned = struct {
        \\    buf: []u8,
        \\    pub fn deinit(self: *Owned) void { self.buf.len = 0; }
        \\};
        \\const Owner = struct {
        \\    item: ?Owned,
        \\    pub fn lazyEnsure(this: *Owner) void {
        \\        const existing: ?*Owned = if (this.item) |*v| v else null;
        \\        const _ = existing orelse {
        \\            this.item = .{ .buf = &[_]u8{} };
        \\            return;
        \\        };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
