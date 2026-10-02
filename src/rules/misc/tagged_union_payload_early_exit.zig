//! Tagged-union payload early-exit detector.  An assignment
//!   `<path> = .{ .<Tag> = <expr> };`
//! where `<expr>` contains a `try` (or `catch ... { return; }` shape
//! captured by keyword_try) causes the union tag to be written to the
//! result location BEFORE the payload expression is evaluated.  If the
//! payload expression exits early via `try`, the LHS is left with the
//! new tag but the payload bytes from the PREVIOUS variant — garbage
//! state that later code (including errdefer cleanups) may misinterpret.
//!
//! Real-world: oven-sh/bun#29422.
//!
//! Fix: hoist the fallible expression into a `const` before the literal:
//!   const val = try computeErr();
//!   resolve.value = .{ .err = val };

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const file_model = @import("../../model/file_model.zig");
const local_bindings = @import("../../model/local_bindings.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const R = "tagged-union-payload-early-exit";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .tagged_union_payload_early_exit)) return;
    const model = try cache.fileModel();

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        try checkBody(gpa, tree, cache, model, entry.proto, entry.body, problems);
    }
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    const bindings = try cache.localBindings(proto, body);

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // RHS must start with `= .{ .<Tag> =`
        if (tags[t] != .equal) continue;
        if (t + 4 > last) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .l_brace) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;

        // Must be a SINGLE-field literal (tagged union variant, not a plain struct).
        if (literalHasTopLevelComma(tags, t + 1, last)) continue;

        // Verify the `=` is an assignment to an existing location, not a
        // `const`/`var` declaration.  Walk back from t-1 across the LHS path.
        if (t == 0) continue;
        var lhs_end: Ast.TokenIndex = t;
        lhs_end -= 1;
        if (tags[lhs_end] != .identifier) continue;
        var lhs_start: Ast.TokenIndex = lhs_end;
        while (lhs_start >= 2 and tags[lhs_start - 1] == .period and tags[lhs_start - 2] == .identifier) {
            lhs_start -= 2;
        }
        // The token before the LHS path must be a statement boundary.
        if (lhs_start > first) {
            const prev = tags[lhs_start - 1];
            const ok = prev == .semicolon or prev == .l_brace or
                prev == .r_brace or prev == .keyword_return or
                prev == .equal_angle_bracket_right or prev == .pipe;
            if (!ok) continue;
        }

        // The target must resolve to a tagged union.  A known struct or
        // untagged union is not this rule's bug class; unknown types remain
        // conservative and continue to the diagnostic.
        switch (targetKind(tree, model, bindings, lhs_start, lhs_end, t)) {
            .not_tagged_union => continue,
            .tagged_union, .unknown => {},
        }
        if (!assignmentIsObservable(tree, tags, bindings, first, last, t, lhs_start))
            continue;

        // Find the matching `}` of the outer literal.
        const rbrace = matchBrace(tags, t + 2, last) orelse continue;

        // Scan inside `.{ ... }` for `keyword_try`; fire at the first one.
        var u: Ast.TokenIndex = t + 3;
        while (u < rbrace) : (u += 1) {
            if (tags[u] == .keyword_try) {
                try report(gpa, problems, tree, u);
                break;
            }
        }
        t = rbrace;
    }
}

/// True iff the anonymous literal at `period_tok` (`.` followed by `{`)
/// has MORE THAN ONE top-level field — `.{ .a = …, .b = … }`.
fn literalHasTopLevelComma(
    tags: []const std.zig.Token.Tag,
    period_tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (period_tok + 1 > last) return false;
    if (tags[period_tok + 1] != .l_brace) return false;
    const rbrace = matchBrace(tags, period_tok + 1, last) orelse return false;
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var fields: u32 = 0;
    var t: Ast.TokenIndex = period_tok + 2;
    while (t + 2 < rbrace) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            },
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .period => if (paren == 0 and brace == 0 and bracket == 0) {
                if (tags[t + 1] == .identifier and tags[t + 2] == .equal) {
                    fields += 1;
                    if (fields > 1) return true;
                }
            },
            else => {},
        }
    }
    return false;
}

const TargetKind = enum {
    tagged_union,
    not_tagged_union,
    unknown,
};

const TypeRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

fn findBindingBefore(
    bindings: *const local_bindings.LocalBindings,
    name: []const u8,
    before: Ast.TokenIndex,
) ?*const local_bindings.Binding {
    var best: ?*const local_bindings.Binding = null;
    for (bindings.items) |*binding| {
        if (!std.mem.eql(u8, binding.name, name) or binding.name_token > before) continue;
        if (best == null or binding.name_token >= best.?.name_token) best = binding;
    }
    return best;
}

fn explicitTypeRange(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    binding: *const local_bindings.Binding,
) ?TypeRange {
    if (binding.name_token >= binding.rhs_first) return null;
    var t = binding.name_token + 1;
    while (t < binding.rhs_first) : (t += 1) {
        if (tags[t] != .colon) continue;
        if (t + 1 >= binding.rhs_first) return null;
        return .{ .first = t + 1, .last = binding.rhs_first - 1 };
    }
    _ = tree;
    return null;
}

fn bindingTypeRange(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    depth: u8,
) ?TypeRange {
    if (depth >= 8) return null;
    if (binding.origin == .param) {
        return .{ .first = binding.rhs_first, .last = binding.rhs_last };
    }
    if (explicitTypeRange(tree, tags, binding)) |range| return range;
    return switch (binding.origin) {
        .alias => |source| blk: {
            const source_binding = findBindingBefore(bindings, source, binding.name_token) orelse
                break :blk null;
            break :blk bindingTypeRange(tree, tags, bindings, source_binding, depth + 1);
        },
        else => null,
    };
}

fn terminalTypeName(tree: *const Ast, range: TypeRange) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    var last: ?Ast.TokenIndex = null;
    var t = range.first;
    while (t <= range.last) : (t += 1) {
        if (tags[t] == .identifier) last = t;
    }
    return if (last) |tok| tree.tokenSlice(tok) else null;
}

fn targetKind(
    tree: *const Ast,
    model: *const file_model.FileModel,
    bindings: *const local_bindings.LocalBindings,
    lhs_start: Ast.TokenIndex,
    lhs_end: Ast.TokenIndex,
    use_tok: Ast.TokenIndex,
) TargetKind {
    const tags = tree.tokens.items(.tag);
    const root_name = tree.tokenSlice(lhs_start);
    const binding = findBindingBefore(bindings, root_name, use_tok) orelse return .unknown;
    const range = bindingTypeRange(tree, tags, bindings, binding, 0) orelse return .unknown;
    const type_name = terminalTypeName(tree, range) orelse return .unknown;
    var type_info = model.findType(type_name) orelse return .unknown;

    var field_tok = lhs_start + 1;
    while (field_tok < lhs_end) : (field_tok += 2) {
        if (field_tok + 1 > lhs_end or tags[field_tok] != .period or
            tags[field_tok + 1] != .identifier)
            return .unknown;
        type_info = model.resolveFieldTypeQualifiedTi(
            type_info,
            tree.tokenSlice(field_tok + 1),
        ) orelse return .unknown;
    }
    if (type_info.kind != .union_) return .not_tagged_union;
    return if (typeInfoIsTaggedUnion(model, type_info)) .tagged_union else .not_tagged_union;
}

fn typeInfoIsTaggedUnion(
    model: *const file_model.FileModel,
    type_info: *const file_model.TypeInfo,
) bool {
    const tags = model.tree.tokens.items(.tag);
    var union_tok = type_info.body_first;
    while (union_tok > 0 and tags[union_tok] != .keyword_union) : (union_tok -= 1) {}
    if (union_tok + 2 >= model.tree.tokens.len or tags[union_tok + 1] != .l_paren)
        return false;
    var depth: u32 = 1;
    var t = union_tok + 2;
    while (t < model.tree.tokens.len and depth > 0) : (t += 1) {
        if (tags[t] == .l_paren) depth += 1 else if (tags[t] == .r_paren) depth -= 1;
    }
    return depth == 0 and t > union_tok + 3;
}

fn typeRangeStartsPointer(tree: *const Ast, range: TypeRange) bool {
    const tags = tree.tokens.items(.tag);
    var t = range.first;
    while (t <= range.last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => {},
            .asterisk => return true,
            else => return false,
        }
    }
    return false;
}

fn assignmentIsObservable(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    lhs_start: Ast.TokenIndex,
) bool {
    const root_name = tree.tokenSlice(lhs_start);
    const binding = findBindingBefore(bindings, root_name, assignment_tok) orelse return true;
    if (binding.origin == .param) return true;
    if (bindingTypeRange(tree, tags, bindings, binding, 0)) |range| {
        if (typeRangeStartsPointer(tree, range)) return true;
    } else {
        return true;
    }
    if (hasDeferredObserver(tree, tags, body_first, body_last, assignment_tok, root_name))
        return true;
    return hasEscapedAddressAlias(
        tree,
        tags,
        bindings,
        body_first,
        body_last,
        assignment_tok,
        root_name,
    );
}

fn hasDeferredObserver(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    root_name: []const u8,
) bool {
    if (assignment_tok <= first) return false;
    var t = first;
    while (t < assignment_tok) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_defer and tags[t] != .keyword_errdefer) continue;
        const end = tokens.skipDeferStmt(tags, t, last) orelse return true;
        var u = t + 1;
        while (u <= end and u < assignment_tok) : (u += 1) {
            if (tags[u] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(u), root_name) and
                (u == 0 or tags[u - 1] != .period))
                return true;
        }
        t = end;
    }
    return false;
}

fn hasEscapedAddressAlias(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    assignment_tok: Ast.TokenIndex,
    root_name: []const u8,
) bool {
    for (bindings.items) |*binding| {
        if (binding.name_token >= assignment_tok) continue;
        if (!bindingAliasesRoot(bindings, binding, root_name, 0)) continue;
        if (addressAliasEscapes(tree, tags, first, last, binding.name, binding.name_token))
            return true;
    }
    return false;
}

fn bindingAliasesRoot(
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    root_name: []const u8,
    depth: u8,
) bool {
    if (depth >= 8) return false;
    return switch (binding.origin) {
        .addr_of => |source| std.mem.eql(u8, source, root_name),
        .alias => |source| blk: {
            const source_binding = findBindingBefore(bindings, source, binding.name_token) orelse
                break :blk false;
            break :blk bindingAliasesRoot(bindings, source_binding, root_name, depth + 1);
        },
        else => false,
    };
}

fn addressAliasEscapes(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    alias_name: []const u8,
    alias_tok: Ast.TokenIndex,
) bool {
    var t = alias_tok + 1;
    while (t < last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), alias_name))
            continue;
        if (t > first and tags[t - 1] == .period) continue;
        // Discarding an alias is not an escape.
        if (t >= 2 and tags[t - 1] == .equal and
            tags[t - 2] == .identifier and std.mem.eql(u8, tree.tokenSlice(t - 2), "_"))
            continue;
        // Copying an alias to another local is followed through by the
        // LocalBindings chain; the copy itself is not the escape.
        if (isLocalAliasCopy(tags, t, first)) continue;
        return true;
    }
    return false;
}

fn isLocalAliasCopy(
    tags: []const std.zig.Token.Tag,
    alias_tok: Ast.TokenIndex,
    first: Ast.TokenIndex,
) bool {
    if (alias_tok < first + 3 or tags[alias_tok - 1] != .equal or
        tags[alias_tok - 2] != .identifier)
        return false;
    const name_tok = alias_tok - 2;
    if (name_tok == first) return false;
    return tags[name_tok - 1] == .keyword_const or tags[name_tok - 1] == .keyword_var;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    try_tok: Ast.TokenIndex,
) !void {
    const msg = try gpa.dupe(u8, "`try` inside single-field union literal assignment — if the error propagates, the tag is written but the payload is left from the previous variant; hoist the `try` before the literal");
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, try_tok),
        .end = Pos.fromTokenEnd(tree, try_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "tagged-union-payload-early-exit: try in single-field literal fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Self = struct {
        \\    state: union(enum) { ok: u32, err: u32 },
        \\    pub fn run(self: *Self) !void {
        \\        self.state = .{ .err = try computeErr() };
        \\    }
        \\};
        \\fn computeErr() !u32 { return 0; }
        \\
    );
}

test "tagged-union-payload-early-exit: no try does not fire" {
    try testing.expectNoFire(check,
        \\const Self = struct {
        \\    state: union(enum) { ok: u32, err: u32 },
        \\    pub fn run(self: *Self) void {
        \\        self.state = .{ .err = computeErr() };
        \\    }
        \\};
        \\fn computeErr() u32 { return 0; }
        \\
    );
}

test "tagged-union-payload-early-exit: const declaration with try does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn run() !void {
        \\    const x = .{ .err = try f() };
        \\    _ = x;
        \\}
        \\fn f() !u32 { return 0; }
        \\
    );
}

test "tagged-union-payload-early-exit: multi-field literal with try does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    state: struct { a: u32, b: u32 },
        \\    pub fn run(self: *Self) !void {
        \\        self.state = .{ .a = 1, .b = try f() };
        \\    }
        \\};
        \\fn f() !u32 { return 0; }
        \\
    );
}

test "skript residual: single-field struct target with try does not fire" {
    try testing.expectNoFire(check,
        \\const Box = struct { value: u32 };
        \\const Self = struct {
        \\    box: Box,
        \\    fn update(self: *Self) !void {
        \\        self.box = .{ .value = try compute() };
        \\    }
        \\};
        \\fn compute() !u32 { return 1; }
        \\
    );
}

test "skript residual: unobserved local tagged-union field with try does not fire" {
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    switch (source.metric) {
        \\        .diagonal => |weights| {
        \\            result.metric = .{ .diagonal = try dupe(weights) };
        \\        },
        \\        else => {},
        \\    }
        \\    return result;
        \\}
        \\fn dupe(weights: []const f64) ![]const f64 { return weights; }
        \\
    );
}

test "skript residual: observed local tagged-union field with try still fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct {
        \\    metric: Metric,
        \\    fn deinit(self: *SpaceSpec) void { _ = self.metric; }
        \\};
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    errdefer result.deinit();
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "skript residual: pointer-owned tagged-union field with try still fires" {
    try testing.expectFires(check, R,
        \\const State = union(enum) { ready: u32, failed: u32 };
        \\const Self = struct {
        \\    state: State,
        \\    fn update(self: *Self) !void {
        \\        self.state = .{ .failed = try compute() };
        \\    }
        \\};
        \\fn compute() !u32 { return 1; }
        \\
    );
}

test "skript residual: explicit local tagged-union field with try does not fire" {
    try testing.expectNoFire(check,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn cloneRegistration(source: SpaceSpec) !SpaceSpec {
        \\    var result: SpaceSpec = .{ .metric = .none };
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "skript residual: plain defer observer still fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct {
        \\    metric: Metric,
        \\    fn deinit(self: *SpaceSpec) void { _ = self.metric; }
        \\};
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    defer result.deinit();
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}

test "skript residual: escaped address alias still fires" {
    try testing.expectFires(check, R,
        \\const Metric = union(enum) { none, diagonal: []const f64 };
        \\const SpaceSpec = struct { metric: Metric };
        \\fn observe(_: *SpaceSpec) void {}
        \\fn cloneSpec(source: SpaceSpec) !SpaceSpec {
        \\    var result = source;
        \\    const alias = &result;
        \\    observe(alias);
        \\    result.metric = .{ .diagonal = try dupe() };
        \\    return result;
        \\}
        \\fn dupe() ![]const f64 { return &.{}; }
        \\
    );
}
