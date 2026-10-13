//! Source-proved prefix preservation and returned enumeration bounds.
//! These are storage/bound facts, not value-defined or whole-array certificates.
const std = @import("std");
const Ast = std.zig.Ast;
const tokens = @import("../ast/tokens.zig");
const Iterator = @import("type_engine").AstIterator;
const FileCache = @import("file_cache.zig").FileCache;
const fresh_storage = @import("fresh_storage.zig");

pub const Selection = struct { parameter: u32, path: []const u8 = "" };
pub const Fill = struct { output: Selection, counter: Selection };

fn names(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    return tree.nodeTag(node) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
}
fn selected(tree: *const Ast, node: Ast.Node.Index, root: []const u8, path: []const u8) bool {
    if (path.len == 0) {
        if (tree.nodeTag(node) == .deref) return names(tree, tree.nodeData(node).node, root);
        return names(tree, node, root);
    }
    if (tree.nodeTag(node) != .field_access) return false;
    const base, const token = tree.nodeData(node).node_and_token;
    return names(tree, base, root) and std.mem.eql(u8, tree.tokenSlice(token), path);
}
fn mentions(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    var token = tree.firstToken(node);
    const last = tree.lastToken(node);
    while (token <= last) : (token += 1) {
        if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), name)) return true;
    }
    return false;
}
fn statements(tree: *const Ast, node: Ast.Node.Index, buffer: *[2]Ast.Node.Index) []const Ast.Node.Index {
    return switch (tree.nodeTag(node)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(node).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const pair = tree.nodeData(node).opt_node_and_opt_node;
            var n: usize = 0;
            if (pair[0].unwrap()) |a| { buffer[n] = a; n += 1; }
            if (pair[1].unwrap()) |a| { buffer[n] = a; n += 1; }
            break :blk buffer[0..n];
        },
        else => &.{},
    };
}

const Proof = struct {
    tree: *const Ast,
    output: []const u8,
    array_path: []const u8,
    counter: []const u8,
    counter_path: []const u8,
    cache: ?*FileCache = null,
    canonical: ?FileCache.ActualCallSummary = null,
    chain: []const Visit = &.{},
    pending: bool = false,
    alias: ?[]const u8 = null,
    pushed: bool = false,
    receiver_only: bool = false,

    fn count(self: *const Proof, node: Ast.Node.Index) bool {
        return selected(self.tree, node, self.counter, self.counter_path);
    }
    fn slot(self: *const Proof, node: Ast.Node.Index) bool {
        if (self.tree.nodeTag(node) != .array_access) return false;
        const base, const index = self.tree.nodeData(node).node_and_node;
        return selected(self.tree, base, self.output, self.array_path) and
            (self.count(index) or (if (self.alias) |alias| names(self.tree, index, alias) else false));
    }
    fn call(self: *Proof, node: Ast.Node.Index, depth: usize) bool {
        const tree = self.tree;
        const touches = mentions(tree, node, self.output) or mentions(tree, node, self.counter);
        const cache = self.cache orelse return false;
        const canonical = self.canonical orelse return false;
        const declaring = cacheFor(cache, canonical) orelse return false;
        const resolver = declaring.zls orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const call_node = tree.fullCall(&buffer, node) orelse return false;
        const frame = resolver.frameForFunction(canonical.callee.reference);
        if (!touches) return !(declaring.callResultMayBeUndefinedAt(fresh_storage.calleeQueryToken(tree, call_node), frame) catch return false);
        const actual = declaring.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call_node), frame) catch return false;
        const callee = actual orelse return false;
        const child_tree = callee.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(child_tree, &proto_buffer, callee.callee.declaration) orelse return false;
        var output: ?Selection = null;
        var counter: ?Selection = null;
        var parameters = proto.iterate(child_tree);
        var ordinal: u32 = 0;
        while (parameters.next()) |_| : (ordinal += 1) {
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const arg = (callee.callArgumentFor(declaring, &argument_buffer, ordinal) catch return false) orelse return false;
            if (selected(tree, arg, self.output, self.array_path)) {
                if (output != null) return false;
                output = .{ .parameter = ordinal };
            } else if (names(tree, arg, self.counter)) {
                if (counter != null) return false;
                counter = .{ .parameter = ordinal, .path = self.counter_path };
            } else if (mentions(tree, arg, self.output) or mentions(tree, arg, self.counter)) return false;
        }
        const fill: Fill = .{ .output = output orelse return false, .counter = counter orelse return false };
        if (!prove(declaring, callee, fill, self.chain, depth + 1)) return false;
        self.pending = false;
        self.alias = null;
        self.pushed = true;
        return true;
    }
    fn walk(self: *Proof, node: Ast.Node.Index, depth: usize) bool {
        if (depth >= 64) return false;
        const tree = self.tree;
        const tag = tree.nodeTag(node);
        if (names(tree, node, "undefined")) return false;
        switch (tag) {
            .fn_decl => return false,
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                var buffer: [2]Ast.Node.Index = undefined;
                for (statements(tree, node, &buffer)) |statement| if (!self.walk(statement, depth + 1)) return false;
                return true;
            },
            .assign_add => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                if (self.count(lhs)) {
                    if (!self.pending or tree.nodeTag(rhs) != .number_literal or !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(rhs)), "1")) return false;
                    self.pending = false;
                    self.alias = null;
                    self.pushed = true;
                    return true;
                }
                if (mentions(tree, lhs, self.counter) or mentions(tree, lhs, self.output)) return false;
            },
            .assign => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                if (self.slot(lhs)) {
                    if (mentions(tree, rhs, "undefined") or mentions(tree, rhs, self.output) or mentions(tree, rhs, self.counter)) return false;
                    if (!self.walk(rhs, depth + 1)) return false;
                    self.pending = true;
                    return true;
                }
                if (self.count(lhs) or selected(tree, lhs, self.output, self.array_path)) return false;
                if (names(tree, lhs, self.counter) or names(tree, lhs, self.output)) return false;
                if (self.receiver_only and mentions(tree, lhs, self.output)) return false;
                if (self.alias) |alias| if (mentions(tree, lhs, alias)) return false;
                // Other fields of the counter record are independent storage.
                if (mentions(tree, rhs, self.output) or mentions(tree, rhs, self.counter)) return false;
                return self.walk(rhs, depth + 1);
            },
            .if_simple, .@"if" => {
                const branch = tree.fullIf(node).?;
                if (branch.payload_token != null and
                    (mentions(tree, branch.ast.cond_expr, self.output) or mentions(tree, branch.ast.cond_expr, self.counter))) return false;
                if (!self.walk(branch.ast.cond_expr, depth + 1)) return false;
                var yes = self.*;
                var no = self.*;
                if (!yes.walk(branch.ast.then_expr, depth + 1)) return false;
                if (branch.ast.else_expr.unwrap()) |other| if (!no.walk(other, depth + 1)) return false;
                self.pending = yes.pending and no.pending;
                self.alias = null;
                self.pushed = yes.pushed or no.pushed;
                return true;
            },
            .while_simple, .while_cont, .@"while", .for_simple, .@"for" => {
                self.pending = false;
                self.alias = null;
                if (tree.fullWhile(node)) |loop| {
                    if (!self.walk(loop.ast.cond_expr, depth + 1) or !self.walk(loop.ast.then_expr, depth + 1)) return false;
                    if (loop.ast.cont_expr.unwrap()) |continuation| if (!self.walk(continuation, depth + 1)) return false;
                    if (loop.ast.else_expr.unwrap()) |other| if (!self.walk(other, depth + 1)) return false;
                } else {
                    const loop = tree.fullFor(node).?;
                    for (loop.ast.inputs) |input| {
                        if (mentions(tree, input, self.output) or mentions(tree, input, self.counter)) return false;
                        if (!self.walk(input, depth + 1)) return false;
                    }
                    if (!self.walk(loop.ast.then_expr, depth + 1)) return false;
                    if (loop.ast.else_expr.unwrap()) |other| if (!self.walk(other, depth + 1)) return false;
                }
                self.pending = false;
                self.alias = null;
                return true;
            },
            .@"switch", .switch_comma => {
                const selection = tree.fullSwitch(node).?;
                if (!self.walk(selection.ast.condition, depth + 1)) return false;
                for (selection.ast.cases) |case| {
                    var arm = self.*;
                    arm.pending = false;
                    if (!arm.walk(tree.fullSwitchCase(case).?.ast.target_expr, depth + 1)) return false;
                    self.pushed = self.pushed or arm.pushed;
                }
                self.pending = false;
                self.alias = null;
                return true;
            },
            .@"defer", .@"errdefer", .address_of => {
                if (mentions(tree, node, self.counter) or mentions(tree, node, self.output)) return false;
            },
            .assign_sub, .assign_sub_wrap, .assign_add_wrap, .assign_mul, .assign_div,
            .assign_mod, .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            .assign_shl, .assign_shr, .assign_shl_sat, .assign_mul_wrap,
            .assign_add_sat, .assign_sub_sat, .assign_mul_sat => {
                const lhs = tree.nodeData(node).node_and_node[0];
                if (mentions(tree, lhs, self.counter) or mentions(tree, lhs, self.output)) return false;
            },
            else => {},
        }
        if (tree.fullVarDecl(node)) |decl| {
            const name = tree.tokenSlice(decl.ast.mut_token + 1);
            if (self.alias) |alias| if (std.mem.eql(u8, name, alias)) return false;
            if (std.mem.eql(u8, name, self.counter) or std.mem.eql(u8, name, self.output)) return false;
            if (decl.ast.init_node.unwrap()) |init| {
                if (self.count(init)) {
                    if (tree.tokenTag(decl.ast.mut_token) != .keyword_const) return false;
                    self.alias = name;
                    return true;
                }
                if (mentions(tree, init, self.output) or names(tree, init, self.counter)) return false;
                return self.walk(init, depth + 1);
            }
            return true;
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, node) != null) return self.call(node, depth);
        var builtin_buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&builtin_buffer, node) != null and
            (mentions(tree, node, self.output) or mentions(tree, node, self.counter))) return false;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| if (!self.walk(child, depth + 1)) return false;
        return true;
    }
};
const Visit = struct { tree: *const Ast, declaration: Ast.Node.Index, fill: Fill };
fn cacheFor(cache: *FileCache, actual: FileCache.ActualCallSummary) ?*FileCache {
    return actual.declaringCache(cache) catch null;
}
fn formal(tree: *const Ast, declaration: Ast.Node.Index, ordinal: u32) ?[]const u8 {
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(tree);
    var index: u32 = 0;
    while (parameters.next()) |parameter| : (index += 1) if (index == ordinal) return tree.tokenSlice(parameter.name_token orelse return null);
    return null;
}
fn equalSelection(a: Selection, b: Selection) bool {
    return a.parameter == b.parameter and std.mem.eql(u8, a.path, b.path);
}
fn prove(cache: *FileCache, actual: FileCache.ActualCallSummary, fill: Fill, chain: []const Visit, depth: usize) bool {
    if (depth >= 64 or chain.len == 64) return false;
    const tree = actual.callee.tree;
    for (chain) |visit| if (visit.tree == tree and visit.declaration == actual.callee.declaration and equalSelection(visit.fill.output, fill.output) and equalSelection(visit.fill.counter, fill.counter)) return true;
    var next: [64]Visit = undefined;
    @memcpy(next[0..chain.len], chain);
    next[chain.len] = .{ .tree = tree, .declaration = actual.callee.declaration, .fill = fill };
    var proof: Proof = .{ .tree = tree, .output = formal(tree, actual.callee.declaration, fill.output.parameter) orelse return false,
        .array_path = fill.output.path, .counter = formal(tree, actual.callee.declaration, fill.counter.parameter) orelse return false,
        .counter_path = fill.counter.path, .cache = cache, .canonical = actual, .chain = next[0 .. chain.len + 1] };
    const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return false;
    return proof.walk(body, 0);
}

pub fn preserves(cache: *FileCache, actual: FileCache.ActualCallSummary, fill: Fill) bool {
    return prove(cache, actual, fill, &.{}, 0);
}

pub fn proveBody(tree: *const Ast, declaration: Ast.Node.Index, output: []const u8, array_path: []const u8, counter: []const u8, counter_path: []const u8) bool {
    var proof: Proof = .{ .tree = tree, .output = output, .array_path = array_path, .counter = counter, .counter_path = counter_path,
        .receiver_only = std.mem.eql(u8, output, counter) and array_path.len != 0 and counter_path.len != 0 };
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    return proof.walk(body, 0) and proof.pushed;
}

const Enumeration = struct {
    tree: *const Ast,
    parameter: []const u8,
    capture: ?[]const u8 = null,
    returned: bool = false,
    fn walk(self: *Enumeration, node: Ast.Node.Index, depth: usize) bool {
        if (depth == 64) return false;
        const tree = self.tree;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
            if (names(tree, value, "null")) return true;
            if (tree.nodeTag(value) == .field_access and tree.tokenTag(tree.firstToken(value)) == .keyword_error) return true;
            if (self.capture) |capture| if (names(tree, value, capture)) { self.returned = true; return true; };
            return false;
        }
        if (tree.fullFor(node)) |loop| {
            var capture = loop.payload_token;
            var slice_seen = false;
            var index: ?[]const u8 = null;
            for (loop.ast.inputs) |input| {
                const pointer = tree.tokenTag(capture) == .asterisk;
                const current = capture + @as(u32, @intFromBool(pointer));
                if (names(tree, input, self.parameter)) slice_seen = true;
                if (tree.nodeTag(input) == .for_range) {
                    const range = tree.nodeData(input).node_and_opt_node;
                    if (tree.nodeTag(range[0]) == .number_literal and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(range[0])), "0") and range[1] == .none) index = tree.tokenSlice(current);
                }
                capture = current + 2;
            }
            const saved = self.capture;
            if (slice_seen and index != null) self.capture = index;
            if (!self.walk(loop.ast.then_expr, depth + 1)) return false;
            self.capture = saved;
            if (loop.ast.else_expr.unwrap()) |other| if (!self.walk(other, depth + 1)) return false;
            return true;
        }
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.fullVarDecl(node)) |decl| {
            const name = tree.tokenSlice(decl.ast.mut_token + 1);
            if (std.mem.eql(u8, name, self.parameter) or (if (self.capture) |capture| std.mem.eql(u8, name, capture) else false)) return false;
        }
        const tag = tree.nodeTag(node);
        if (tag == .address_of) {
            if (mentions(tree, node, self.parameter) or (if (self.capture) |capture| mentions(tree, node, capture) else false)) return false;
        }
        switch (tag) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap, .assign_add_sat,
            .assign_sub_sat, .assign_mul_sat, .assign_shl, .assign_shr,
            .assign_shl_sat, .assign_bit_and, .assign_bit_or, .assign_bit_xor => {
                const lhs = tree.nodeData(node).node_and_node[0];
                if (mentions(tree, lhs, self.parameter) or (if (self.capture) |capture| mentions(tree, lhs, capture) else false)) return false;
            },
            else => {},
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| if (!self.walk(child, depth + 1)) return false;
        return true;
    }
};

pub fn returnedIndexParameter(tree: *const Ast, declaration: Ast.Node.Index) ?u32 {
    const body = tokens.bodyOf(tree, declaration) orelse return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(tree);
    var ordinal: u32 = 0;
    while (parameters.next()) |parameter| : (ordinal += 1) {
        const token = parameter.name_token orelse continue;
        const ty = parameter.type_expr orelse continue;
        const first = tree.firstToken(ty);
        if (tree.tokenTag(first) != .l_bracket or tree.tokenTag(first + 1) != .r_bracket) continue;
        var proof: Enumeration = .{ .tree = tree, .parameter = tree.tokenSlice(token) };
        if (proof.walk(body, 0) and proof.returned) return ordinal;
    }
    return null;
}

fn parameterSelection(tree: *const Ast, declaration: Ast.Node.Index, node: Ast.Node.Index) ?Selection {
    var root = node;
    var path: []const u8 = "";
    if (tree.nodeTag(root) == .deref) root = tree.nodeData(root).node;
    if (tree.nodeTag(root) == .field_access) {
        const base, const token = tree.nodeData(root).node_and_token;
        root = base;
        path = tree.tokenSlice(token);
    }
    if (tree.nodeTag(root) != .identifier) return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(tree);
    var ordinal: u32 = 0;
    while (parameters.next()) |parameter| : (ordinal += 1) {
        const token = parameter.name_token orelse continue;
        if (names(tree, root, tree.tokenSlice(token))) return .{ .parameter = ordinal, .path = path };
    }
    return null;
}

fn appendFill(result: *[8]Fill, count: *usize, fill: Fill) void {
    for (result[0..count.*]) |previous|
        if (equalSelection(previous.output, fill.output) and equalSelection(previous.counter, fill.counter)) return;
    if (count.* == result.len) return;
    result[count.*] = fill;
    count.* += 1;
}

fn candidates(cache: *FileCache, actual: FileCache.ActualCallSummary, node: Ast.Node.Index, result: *[8]Fill, count: *usize, depth: usize, declarations: usize) void {
    if (depth == 64 or declarations == 8) return;
    const tree = actual.callee.tree;
    if (tree.nodeTag(node) == .assign_add) {
        const counter = parameterSelection(tree, actual.callee.declaration, tree.nodeData(node).node_and_node[0]) orelse return;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, actual.callee.declaration) orelse return;
        var parameters = proto.iterate(tree);
        var ordinal: u32 = 0;
        while (parameters.next()) |parameter| : (ordinal += 1) {
            const ty = parameter.type_expr orelse continue;
            const first = tree.firstToken(ty);
            if (tree.tokenTag(first) != .asterisk or tree.tokenTag(first + 1) != .l_bracket) continue;
            appendFill(result, count, .{ .output = .{ .parameter = ordinal }, .counter = counter });
        }
    }
    var call_buffer: [1]Ast.Node.Index = undefined;
    if (tree.fullCall(&call_buffer, node)) |call| {
        // Follow only calls forwarding at least two parameter roots. No
        // spelling identifies a helper and no unrelated call tree is opened.
        var roots: usize = 0;
        for (call.ast.params) |argument| if (parameterSelection(tree, actual.callee.declaration, argument) != null) { roots += 1; };
        if (roots >= 2) {
            const declaring = cacheFor(cache, actual) orelse return;
            const resolver = declaring.zls orelse return;
            const frame = resolver.frameForFunction(actual.callee.reference);
            const child = (declaring.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call), frame) catch null) orelse return;
            if (child.callee.tree == tree and child.callee.declaration == actual.callee.declaration) return;
            const body = tokens.bodyOf(child.callee.tree, child.callee.declaration) orelse return;
            var found: [8]Fill = undefined;
            var found_count: usize = 0;
            candidates(declaring, child, body, &found, &found_count, 0, declarations + 1);
            for (found[0..found_count]) |fill| {
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const output_arg = (child.callArgumentFor(declaring, &argument_buffer, fill.output.parameter) catch null) orelse continue;
                const counter_arg = (child.callArgumentFor(declaring, &argument_buffer, fill.counter.parameter) catch null) orelse continue;
                var output = parameterSelection(tree, actual.callee.declaration, output_arg) orelse continue;
                var counter = parameterSelection(tree, actual.callee.declaration, counter_arg) orelse continue;
                if (output.path.len != 0 and fill.output.path.len != 0) continue;
                if (counter.path.len != 0 and fill.counter.path.len != 0) continue;
                if (fill.output.path.len != 0) output.path = fill.output.path;
                if (fill.counter.path.len != 0) counter.path = fill.counter.path;
                appendFill(result, count, .{ .output = output, .counter = counter });
            }
        }
        return;
    }
    var children = Iterator.init(tree, node);
    while (children.next(tree)) |child| candidates(cache, actual, child, result, count, depth + 1, declarations);
}

pub fn fills(cache: *FileCache, actual: FileCache.ActualCallSummary, result: *[8]Fill) usize {
    const body = tokens.bodyOf(actual.callee.tree, actual.callee.declaration) orelse return 0;
    var found: [8]Fill = undefined;
    var found_count: usize = 0;
    candidates(cache, actual, body, &found, &found_count, 0, 0);
    var count: usize = 0;
    for (found[0..found_count]) |fill|
        if (preserves(cache, actual, fill)) { result[count] = fill; count += 1; };
    return count;
}

test "prefix summary: receiver append requires a store before each count step" {
    for ([_]struct { body: []const u8, expected: bool }{
        .{ .body = "if (flag) return; const i = self.len; self.fields[i] = value; self.len += 1;", .expected = true },
        .{ .body = "self.len += 1;", .expected = false },
        .{ .body = "if (flag) self.fields[self.len] = value; self.len += 1;", .expected = false },
        .{ .body = "self.fields[self.len] = undefined; self.len += 1;", .expected = false },
        .{ .body = "self.fields[self.len] = value; self.len = 7;", .expected = false },
        .{ .body = "const alias = self; alias.len += 1;", .expected = false },
        .{ .body = "self.fields[self.len] = value; self.len += 1; self.spare = value;", .expected = false },
        .{ .body = "self.fields[self.len] = value; self.len += 1; self.spare[0] = value;", .expected = false },
    }) |case| {
        const source = try std.fmt.allocPrintSentinel(std.testing.allocator,
            "fn append(self: *Record, flag: bool, value: u8) void {{ {s} }}", .{case.body}, 0);
        defer std.testing.allocator.free(source);
        var tree = try Ast.parse(std.testing.allocator, source, .zig);
        defer tree.deinit(std.testing.allocator);
        try std.testing.expectEqual(case.expected, proveBody(&tree, tree.rootDecls()[0], "self", "fields", "self", "len"));
    }
}

test "prefix summary: returned enumeration rejects alternative return values" {
    for ([_]struct { body: []const u8, expected: bool }{
        .{ .body = "for (values, 0..) |_, i| { if (flag) return i; } return null;", .expected = true },
        .{ .body = "for (values, 0..) |_, i| { if (flag) return i; } return 7;", .expected = false },
        .{ .body = "for (values, 1..) |_, i| { return i; } return null;", .expected = false },
        .{ .body = "for (values, 0..) |_, i| { return i + 1; } return null;", .expected = false },
    }) |case| {
        const source = try std.fmt.allocPrintSentinel(std.testing.allocator,
            "fn find(values: []const u8, flag: bool) ?usize {{ {s} }}", .{case.body}, 0);
        defer std.testing.allocator.free(source);
        var tree = try Ast.parse(std.testing.allocator, source, .zig);
        defer tree.deinit(std.testing.allocator);
        try std.testing.expectEqual(case.expected, returnedIndexParameter(&tree, tree.rootDecls()[0]) != null);
    }
}
