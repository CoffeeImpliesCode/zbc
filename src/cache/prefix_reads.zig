//! Body-proved reads of counted inline array fields.
const std = @import("std");
const Ast = std.zig.Ast;
const tokens = @import("../ast/tokens.zig");
const Iterator = @import("type_engine").AstIterator;

fn names(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    return tree.nodeTag(node) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
}

fn field(tree: *const Ast, node: Ast.Node.Index, root: []const u8, path: []const u8) bool {
    if (tree.nodeTag(node) != .field_access) return false;
    const base, const selector = tree.nodeData(node).node_and_token;
    return names(tree, base, root) and std.mem.eql(u8, tree.tokenSlice(selector), path);
}

const Proof = struct {
    tree: *const Ast,
    parameter: []const u8,
    array_path: []const u8,
    counter_path: []const u8,
    bounded: [16][]const u8 = undefined,
    count: usize = 0,
    read: bool = false,

    fn endpoint(self: *const Proof, node: Ast.Node.Index) bool {
        const tree = self.tree;
        if (field(tree, node, self.parameter, self.counter_path)) return true;
        if (tree.nodeTag(node) == .number_literal and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "0")) return true;
        for (self.bounded[0..self.count]) |name| if (names(tree, node, name)) return true;
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&buffer, node)) |args| {
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@min") or args.len != 2) return false;
            return self.endpoint(args[0]) or self.endpoint(args[1]);
        }
        return false;
    }

    fn walk(self: *Proof, node: Ast.Node.Index, depth: usize) bool {
        if (depth == 64) return false;
        const tree = self.tree;
        if (tree.fullSlice(node)) |slice| {
            if (field(tree, slice.ast.sliced, self.parameter, self.array_path)) {
                if (slice.ast.sentinel != .none or tree.nodeTag(slice.ast.start) != .number_literal or
                    !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(slice.ast.start)), "0")) return false;
                const end = slice.ast.end.unwrap() orelse return false;
                if (!self.endpoint(end)) return false;
                self.read = true;
                return true;
            }
        }
        switch (tree.nodeTag(node)) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap, .assign_add_sat,
            .assign_sub_sat, .assign_mul_sat, .assign_shl, .assign_shr, .assign_shl_sat,
            .assign_bit_and, .assign_bit_or, .assign_bit_xor => {
                const lhs = tree.nodeData(node).node_and_node[0];
                var token = tree.firstToken(lhs);
                const last = tree.lastToken(lhs);
                while (token <= last) : (token += 1) {
                    if (tree.tokenTag(token) != .identifier) continue;
                    const name = tree.tokenSlice(token);
                    if (std.mem.eql(u8, name, self.parameter)) return false;
                    for (self.bounded[0..self.count]) |bound| if (std.mem.eql(u8, name, bound)) return false;
                }
            },
            else => {},
        }
        if (field(tree, node, self.parameter, self.array_path)) return false;
        if (names(tree, node, self.parameter)) return false;
        if (tree.nodeTag(node) == .field_access) {
            const base = tree.nodeData(node).node_and_token[0];
            if (names(tree, base, self.parameter))
                return field(tree, node, self.parameter, self.counter_path);
        }
        if (tree.fullVarDecl(node)) |decl| {
            const name = tree.tokenSlice(decl.ast.mut_token + 1);
            if (std.mem.eql(u8, name, self.parameter)) return false;
            for (self.bounded[0..self.count]) |bound| if (std.mem.eql(u8, name, bound)) return false;
            const init = decl.ast.init_node.unwrap() orelse return true;
            if (tree.tokenTag(decl.ast.mut_token) == .keyword_const and self.endpoint(init)) {
                if (self.count == self.bounded.len) return false;
                self.bounded[self.count] = name;
                self.count += 1;
            }
        }
        // Const declarations cannot be rebound. Taking their address still
        // exposes the bound, so reject aliases rather than guess call effects.
        if (tree.nodeTag(node) == .address_of) {
            const first = tree.firstToken(node);
            const last = tree.lastToken(node);
            var token = first;
            while (token <= last) : (token += 1) {
                if (tree.tokenTag(token) != .identifier) continue;
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, self.parameter)) return false;
                for (self.bounded[0..self.count]) |bound| if (std.mem.eql(u8, name, bound)) return false;
            }
        }
        var call_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&call_buffer, node)) |call| {
            if (tree.nodeTag(call.ast.fn_expr) == .field_access and
                names(tree, tree.nodeData(call.ast.fn_expr).node_and_token[0], self.parameter)) return false;
        }
        var builtin_buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&builtin_buffer, node) != null and
            !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@min")) {
            var token = tree.firstToken(node);
            const last = tree.lastToken(node);
            while (token <= last) : (token += 1) {
                if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), self.parameter)) return false;
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| if (!self.walk(child, depth + 1)) return false;
        return true;
    }
};

pub fn boundedReads(tree: *const Ast, declaration: Ast.Node.Index, parameter: []const u8, array_path: []const u8, counter_path: []const u8) bool {
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var proof: Proof = .{ .tree = tree, .parameter = parameter, .array_path = array_path, .counter_path = counter_path };
    return proof.walk(body, 0) and proof.read;
}

pub const Selection = struct { array_path: []const u8, counter_path: []const u8 };

const Candidates = struct {
    array: ?[]const u8 = null,
    counters: [16][]const u8 = undefined,
    count: usize = 0,

    fn collect(self: *Candidates, tree: *const Ast, node: Ast.Node.Index, parameter: []const u8, depth: usize) bool {
        if (depth == 64) return false;
        if (tree.fullSlice(node)) |slice| {
            if (tree.nodeTag(slice.ast.sliced) == .field_access) {
                const base, const selector = tree.nodeData(slice.ast.sliced).node_and_token;
                if (names(tree, base, parameter)) {
                    const name = tree.tokenSlice(selector);
                    if (self.array) |array| if (!std.mem.eql(u8, array, name)) return false;
                    self.array = name;
                }
            }
        }
        if (tree.nodeTag(node) == .field_access) {
            const base, const selector = tree.nodeData(node).node_and_token;
            if (names(tree, base, parameter)) {
                const name = tree.tokenSlice(selector);
                const duplicate = for (self.counters[0..self.count]) |counter| {
                    if (std.mem.eql(u8, counter, name)) break true;
                } else false;
                if (!duplicate) {
                    if (self.count == self.counters.len) return false;
                    self.counters[self.count] = name;
                    self.count += 1;
                }
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| if (!self.collect(tree, child, parameter, depth + 1)) return false;
        return true;
    }
};

pub fn selection(tree: *const Ast, declaration: Ast.Node.Index, parameter: []const u8) ?Selection {
    const body = tokens.bodyOf(tree, declaration) orelse return null;
    var candidates: Candidates = .{};
    if (!candidates.collect(tree, body, parameter, 0)) return null;
    const array = candidates.array orelse return null;
    for (candidates.counters[0..candidates.count]) |counter| {
        if (std.mem.eql(u8, array, counter)) continue;
        if (boundedReads(tree, declaration, parameter, array, counter))
            return .{ .array_path = array, .counter_path = counter };
    }
    return null;
}

test "field counted prefix: bounded callee read proof rejects altered bounds and escapes" {
    const gpa = std.testing.allocator;
    for ([_]struct { body: []const u8, safe: bool }{
        .{ .body = "const m = @min(a.len, b.len); for (b.fields[0..m]) |x| { _ = x; }", .safe = true },
        .{ .body = "for (b.fields[0..b.len]) |x| { _ = x; }", .safe = true },
        .{ .body = "const m = @min(a.len, b.len); for (b.fields[0..m + 1]) |x| { _ = x; }", .safe = false },
        .{ .body = "b.len += 1; for (b.fields[0..b.len]) |x| { _ = x; }", .safe = false },
        .{ .body = "b.mutate(); for (b.fields[0..b.len]) |x| { _ = x; }", .safe = false },
        .{ .body = "const m = @min(a.len, b.len); escape(&m); for (b.fields[0..m]) |x| { _ = x; }", .safe = false },
        .{ .body = "const m = b.len; { const m = a.len; for (b.fields[0..m]) |x| { _ = x; } }", .safe = false },
    }) |case| {
        const source = try std.fmt.allocPrintSentinel(gpa, "fn read(a: Path, b: Path) void {{ {s} }}", .{case.body}, 0);
        defer gpa.free(source);
        var tree = try Ast.parse(gpa, source, .zig);
        defer tree.deinit(gpa);
        try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
        try std.testing.expectEqual(case.safe, boundedReads(&tree, tree.rootDecls()[0], "b", "fields", "len"));
    }
}
