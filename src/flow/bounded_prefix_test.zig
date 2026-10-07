const std = @import("std");
const proof = @import("bounded_prefix.zig");
const state_mod = @import("abstract_state.zig");
const Ast = std.zig.Ast;

fn fill(source: [:0]const u8) !bool {
    var tree = try Ast.parse(std.testing.allocator, source, .zig);
    defer tree.deinit(std.testing.allocator);
    for (0..tree.nodes.len) |raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.fullFor(node)) |loop| return proof.rangeFill(&tree, loop) != null;
    }
    return false;
}

test "bounded fill accepts normal exhaustion with fallible element creation" {
    try std.testing.expect(try fill("fn f(n: usize) !void { var a: [126]*u8 = undefined; var done: usize = 0; for (0..n) |i| { a[i] = try create(); done += 1; } }"));
}

test "bounded fill rejects shifted conditional skipped and undefined stores" {
    const sources = [_][:0]const u8{
        "fn f(n: usize) void { var a: [8]u8 = undefined; for (1..n) |i| a[i] = 1; }",
        "fn f(n: usize, yes: bool) void { var a: [8]u8 = undefined; for (0..n) |i| { if (yes) a[i] = 1; } }",
        "fn f(n: usize) void { var a: [8]u8 = undefined; for (0..n) |i| { continue; a[i] = 1; } }",
        "fn f(n: usize) void { var a: [8]u8 = undefined; for (0..n) |i| { a[i] = undefined; } }",
        "fn f(n: usize) void { var a: [8]u8 = undefined; for (0..n) |i| { a[i + 1] = 1; } }",
        "fn f(n: usize) void { var a: [8]u8 = undefined; for (0..n) |i| { a[i] = 1; n += 1; } }",
    };
    for (sources) |source| try std.testing.expect(!try fill(source));
}

test "scaled declaration bounds credit two children but not the whole array" {
    const gpa = std.testing.allocator;
    var state: state_mod.AbstractState = .{};
    defer state.deinit(gpa);
    const array: state_mod.LocalId = @enumFromInt(0);
    const count: state_mod.LocalId = @enumFromInt(1);
    const cursor: state_mod.LocalId = @enumFromInt(2);
    const upper: state_mod.LocalId = @enumFromInt(3);
    const start: state_mod.LocalId = @enumFromInt(4);
    const index: state_mod.LocalId = @enumFromInt(5);
    for ([_]state_mod.LocalId{ count, cursor, upper, start, index }) |local| {
        try state.locals.put(gpa, local, .plain);
        try state.nonnegative_locals.put(gpa, local, {});
    }
    try state.setSymbolicPrefix(gpa, array, count, 0, 126);
    const certificate: proof.ScaledIndex = .{ .index = index, .count = count, .cursor = cursor, .upper = upper, .start = start, .scale = 2 };
    try std.testing.expect(!try proof.recordScaledIndex(gpa, &state, certificate));
    _ = try state.assumeComparison(gpa, .{ .lhs = .{ .local = .{ .local = cursor } }, .rhs = .{ .local = .{ .local = upper } }, .op = .lt });
    try std.testing.expect(try proof.recordScaledIndex(gpa, &state, certificate));
    try std.testing.expect(state.hasInitializedElement(array, .{ .local = .{ .local = index } }));
    try std.testing.expect(state.hasInitializedElement(array, .{ .local = .{ .local = index, .offset = 1 } }));
    try std.testing.expect(!state.hasInitializedPrefix(array, 126));
    state.forgetInitializationArray(array);
    try std.testing.expect(!state.hasInitializedElement(array, .{ .local = .{ .local = index } }));
}

test "scaled declaration certificate rejects undefined endpoints" {
    const gpa = std.testing.allocator;
    var state: state_mod.AbstractState = .{};
    defer state.deinit(gpa);
    const certificate: proof.ScaledIndex = .{ .index = @enumFromInt(0), .count = @enumFromInt(1), .cursor = @enumFromInt(2), .upper = @enumFromInt(3), .start = @enumFromInt(4), .scale = 2 };
    for ([_]state_mod.LocalId{ certificate.index, certificate.count, certificate.cursor, certificate.upper, certificate.start }) |local| try state.locals.put(gpa, local, .plain);
    try state.locals.put(gpa, certificate.start, .undef);
    _ = try state.assumeComparison(gpa, .{ .lhs = .{ .local = .{ .local = certificate.cursor } }, .rhs = .{ .local = .{ .local = certificate.upper } }, .op = .lt });
    try std.testing.expect(!try proof.recordScaledIndex(gpa, &state, certificate));
}

fn difference(source: [:0]const u8) !?proof.Difference {
    var tree = try Ast.parse(std.testing.allocator, source, .zig);
    defer tree.deinit(std.testing.allocator);
    const root = tree.rootDecls();
    const declaration = tree.fullVarDecl(root[0]).?;
    return proof.scaledDifference(&tree, declaration.ast.init_node.unwrap().?);
}

test "scaled declaration shape rejects wrapping and incomplete products" {
    const good = (try difference("const n = (upper - start) * 2;")).?;
    try std.testing.expectEqual(@as(u64, 2), good.scale);
    try std.testing.expect((try difference("const n = (upper -% start) * 2;")) == null);
    try std.testing.expect((try difference("const n = (upper - start) *% 2;")) == null);
    try std.testing.expect((try difference("const n = (upper - start) * 0;")) == null);
    try std.testing.expect((try difference("const n = (upper - start) / 2;")) == null);
}

test "bounded prefix leaves uncovered elements and later undefined writes unknown" {
    const gpa = std.testing.allocator;
    var state: state_mod.AbstractState = .{};
    defer state.deinit(gpa);
    const array: state_mod.LocalId = @enumFromInt(0);
    const count: state_mod.LocalId = @enumFromInt(1);
    try state.setScalarValue(gpa, count, 4);
    try state.setSymbolicPrefix(gpa, array, count, 0, 8);
    try std.testing.expect(state.hasInitializedElement(array, .{ .constant = 3 }));
    try std.testing.expect(!state.hasInitializedElement(array, .{ .constant = 4 }));
    try std.testing.expect(!state.hasInitializedPrefix(array, 8));
    try state.setExactElement(gpa, array, 2, false);
    try std.testing.expect(!state.hasInitializedElement(array, .{ .constant = 2 }));
}
