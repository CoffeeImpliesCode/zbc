//! Narrow declaration-derived certificates for initialized runtime prefixes.
//! These helpers do not promote a partial fill to complete-array coverage.
const std = @import("std");
const abstract = @import("abstract_state.zig");
const Ast = std.zig.Ast;

pub const RangeFill = struct {
    array_token: Ast.TokenIndex,
    count_token: Ast.TokenIndex,
    capture_token: Ast.TokenIndex,
    rhs: Ast.Node.Index,
};

/// Shape only. The builder must resolve tokens to their actual bindings,
/// establish a fixed array extent, and check rhsIsDefined/valueInputs.
/// Credit belongs exclusively on the loop's natural exit. No break edge may
/// receive it. The bound must be a defined, unsigned, immutable local.
pub fn rangeFill(tree: *const Ast, loop: Ast.full.For) ?RangeFill {
    if (loop.label_token != null or loop.ast.inputs.len != 1 or loop.ast.else_expr != .none) return null;
    const input = loop.ast.inputs[0];
    const first = tree.firstToken(input);
    const last = tree.lastToken(input);
    if (last != first + 2 or tree.tokenTag(first) != .number_literal or
        !std.mem.eql(u8, tree.tokenSlice(first), "0") or tree.tokenTag(first + 1) != .ellipsis2 or
        tree.tokenTag(last) != .identifier) return null;
    const capture = loop.payload_token;
    if (capture == 0 or capture + 1 >= tree.tokens.len or tree.tokenTag(capture - 1) != .pipe or
        tree.tokenTag(capture) != .identifier or tree.tokenTag(capture + 1) != .pipe or
        std.mem.eql(u8, tree.tokenSlice(capture), "_")) return null;
    const count_name = tree.tokenSlice(last);
    const capture_name = tree.tokenSlice(capture);
    if (std.mem.eql(u8, count_name, capture_name)) return null;
    const body = loop.ast.then_expr;
    var buffer: [2]Ast.Node.Index = undefined;
    const single: [1]Ast.Node.Index = .{body};
    const statements: []const Ast.Node.Index = switch (tree.nodeTag(body)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(body).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const data = tree.nodeData(body).opt_node_and_opt_node;
            buffer[0] = data[0].unwrap() orelse return null;
            if (data[1].unwrap()) |second| {
                buffer[1] = second;
                break :blk buffer[0..2];
            }
            break :blk buffer[0..1];
        },
        else => single[0..],
    };
    var found: ?RangeFill = null;
    for (statements) |statement| {
        if (tree.nodeTag(statement) != .assign) continue;
        const pair = tree.nodeData(statement).node_and_node;
        if (tree.nodeTag(pair[0]) != .array_access) continue;
        const selection = tree.nodeData(pair[0]).node_and_node;
        if (tree.nodeTag(selection[0]) != .identifier or tree.nodeTag(selection[1]) != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(selection[1])), capture_name)) return null;
        if (found != null) return null;
        const rhs = ungroup(tree, pair[1]);
        if (tree.nodeTag(rhs) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(rhs)), "undefined")) return null;
        found = .{ .array_token = tree.nodeMainToken(selection[0]), .count_token = last, .capture_token = capture, .rhs = pair[1] };
    }
    const result = found orelse return null;
    const array_name = tree.tokenSlice(result.array_token);
    if (std.mem.eql(u8, array_name, count_name) or std.mem.eql(u8, array_name, capture_name)) return null;
    var token = tree.firstToken(body);
    const body_last = tree.lastToken(body);
    while (token <= body_last) : (token += 1) {
        switch (tree.tokenTag(token)) {
            .keyword_break, .keyword_continue, .keyword_defer, .keyword_errdefer => return null,
            .identifier => {
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, count_name)) return null;
                if (std.mem.eql(u8, name, array_name) and token != result.array_token) return null;
                // A redeclared capture would change the selected slot.
                if (std.mem.eql(u8, name, capture_name) and token > 0 and
                    (tree.tokenTag(token - 1) == .keyword_const or tree.tokenTag(token - 1) == .keyword_var)) return null;
            },
            else => {},
        }
    }
    return result;
}

pub const Difference = struct {
    upper_token: Ast.TokenIndex,
    start_token: Ast.TokenIndex,
    scale: u64,
};

/// Accept exactly `(upper - start) * positive_literal`, with ordinary
/// checked arithmetic. Wrapping and saturating operators never qualify.
pub fn scaledDifference(tree: *const Ast, expression: Ast.Node.Index) ?Difference {
    const product = ungroup(tree, expression);
    if (tree.nodeTag(product) != .mul) return null;
    const factors = tree.nodeData(product).node_and_node;
    const difference = ungroup(tree, factors[0]);
    const multiplier = ungroup(tree, factors[1]);
    if (tree.nodeTag(difference) != .sub or tree.nodeTag(multiplier) != .number_literal) return null;
    const scale = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(multiplier)), 0) catch return null;
    if (scale == 0) return null;
    const operands = tree.nodeData(difference).node_and_node;
    const upper = ungroup(tree, operands[0]);
    const start = ungroup(tree, operands[1]);
    if (tree.nodeTag(upper) != .identifier or tree.nodeTag(start) != .identifier) return null;
    return .{ .upper_token = tree.nodeMainToken(upper), .start_token = tree.nodeMainToken(start), .scale = scale };
}

fn ungroup(tree: *const Ast, expression: Ast.Node.Index) Ast.Node.Index {
    var node = expression;
    while (tree.nodeTag(node) == .grouped_expression) node = tree.nodeData(node).node_and_token[0];
    return node;
}

pub const ScaledIndex = struct {
    index: abstract.LocalId,
    count: abstract.LocalId,
    cursor: abstract.LocalId,
    upper: abstract.LocalId,
    start: abstract.LocalId,
    scale: u64,
};

/// Builder preconditions: index is a fresh const initialized by
/// `(cursor-start)*scale`; count is a const initialized earlier by
/// `(upper-start)*scale`; the same immutable, unsigned upper/start bindings
/// occur in both declarations; all involved bindings are non-address-taken.
/// Emit immediately after successful index evaluation, never before it.
/// Checked subtraction/multiplication on that path establish nonnegativity
/// and exclude overflow. Under cursor < upper, integer spacing gives
/// index + residue < count for each residue < scale. We record only the
/// two offsets representable by IndexTerm; no complete-array fact is added.
pub fn recordScaledIndex(gpa: std.mem.Allocator, state: *abstract.AbstractState, certificate: ScaledIndex) !bool {
    if (certificate.scale == 0) return false;
    for ([_]abstract.LocalId{ certificate.index, certificate.count, certificate.cursor, certificate.upper, certificate.start }) |local| {
        // Parameters have no declaration transfer and therefore no origin
        // entry. The builder resolves each binding; only explicit undefined
        // origins reject an otherwise valid declaration certificate.
        if (state.locals.get(local)) |origin| {
            if (origin == .undef) return false;
        }
    }
    if (!state.provesLessThan(.{ .local = .{ .local = certificate.cursor } }, .{ .local = .{ .local = certificate.upper } })) return false;
    _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = certificate.index } },
        .rhs = .{ .constant = 0 },
        .op = .ge,
    });
    _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = certificate.index } },
        .rhs = .{ .local = .{ .local = certificate.count } },
        .op = .lt,
    });
    if (certificate.scale >= 2) _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = certificate.index, .offset = 1 } },
        .rhs = .{ .local = .{ .local = certificate.count } },
        .op = .lt,
    });
    return true;
}
