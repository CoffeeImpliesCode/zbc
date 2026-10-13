//! Closed-body syntax evidence, not a purity summary. The declaring cache must
//! prove every call event and charge each node event before asking for more.
const std = @import("std");
const Ast = std.zig.Ast;
const Iterator = @import("type_engine").AstIterator;
const tokens = @import("../ast/tokens.zig");
const LocalBindings = @import("../model/local_bindings.zig").LocalBindings;
const budget_mod = @import("../budget.zig");

pub const Event = union(enum) {
    node: Ast.Node.Index,
    call: Ast.Node.Index,
    write_or_unknown: Ast.Node.Index,
    write: struct {
        node: Ast.Node.Index,
        target: Ast.Node.Index,
        value: Ast.Node.Index,
    },
};

/// Borrows the tree and its body's bindings for the entire scan. No allocation
/// or resolution is performed here. EOF only certifies complete syntax coverage.
pub const Scan = struct {
    const Frame = union(enum) {
        children: Iterator,
        switch_children: struct {
            condition: ?Ast.Node.Index,
            cases: []const Ast.Node.Index,
        },

        fn next(self: *Frame, tree: *const Ast) ?Ast.Node.Index {
            switch (self.*) {
                .children => |*it| return it.next(tree),
                .switch_children => |*it| {
                    if (it.condition) |condition| {
                        it.condition = null;
                        return condition;
                    }
                    if (it.cases.len == 0) return null;
                    const result = it.cases[0];
                    it.cases = it.cases[1..];
                    return result;
                },
            }
        }
    };

    tree: *const Ast,
    fn_decl: Ast.Node.Index,
    bindings: *const LocalBindings,
    frames: [64]Frame = @splat(.{ .children = .{ .array = @splat(.none) } }),
    depth: usize = 1,
    visited: u32 = 0,
    pending: ?Ast.Node.Index = null,
    /// A semantic consumer may narrow the pending node's children only after
    /// proving its instantiated branch. The condition remains in that iterator.
    pending_children: ?Iterator = null,
    invalid_root: bool = false,

    pub fn init(tree: *const Ast, fn_decl: Ast.Node.Index, bindings: *const LocalBindings) Scan {
        var result: Scan = .{ .tree = tree, .fn_decl = fn_decl, .bindings = bindings };
        const body = tokens.bodyOf(tree, fn_decl);
        result.invalid_root = body == null or bindings.tree != tree;
        result.frames[0] = .{ .children = .{ .array = .{
            if (body) |node| node.toOptional() else .none, .none, .none, .none, .none,
        } } };
        return result;
    }

    pub fn next(self: *Scan) budget_mod.BudgetError!?Event {
        if (self.invalid_root) {
            self.invalid_root = false;
            self.depth = 0;
            return .{ .write_or_unknown = self.fn_decl };
        }
        if (self.pending) |node| {
            self.pending = null;
            const narrowed = self.pending_children;
            self.pending_children = null;
            const node_effect = self.effect(node);
            // A nested declaration does not execute its function body. Inline
            // assembly has opaque children the ordinary iterator cannot decode.
            switch (self.tree.nodeTag(node)) {
                .fn_decl, .fn_proto, .fn_proto_one, .fn_proto_multi, .fn_proto_simple, .@"asm", .asm_simple, .asm_input, .asm_output => {},
                else => {
                    const frame: Frame = if (narrowed) |children|
                        .{ .children = children }
                    else if (self.tree.fullSwitch(node)) |sw|
                        .{ .switch_children = .{ .condition = sw.ast.condition, .cases = sw.ast.cases } }
                    else
                        .{ .children = Iterator.init(self.tree, node) };
                    if (self.depth == self.frames.len)
                        return self.exhausted(node, .readonly_call_depth, self.frames.len);
                    self.frames[self.depth] = frame;
                    self.depth += 1;
                },
            }
            if (node_effect) |event| return event;
        }
        while (self.depth != 0) {
            const node = self.frames[self.depth - 1].next(self.tree) orelse {
                self.depth -= 1;
                continue;
            };
            if (self.visited == self.tree.nodes.len)
                return self.exhausted(node, .readonly_call_nodes, @intCast(self.tree.nodes.len));
            self.visited += 1;
            self.pending = node;
            return .{ .node = node };
        }
        return null;
    }

    fn effect(self: *const Scan, node: Ast.Node.Index) ?Event {
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .call, .call_comma, .call_one, .call_one_comma => return .{ .call = node },
            .assign, .assign_mul, .assign_div, .assign_mod, .assign_add, .assign_sub, .assign_shl, .assign_shl_sat, .assign_shr, .assign_bit_and, .assign_bit_xor, .assign_bit_or, .assign_mul_wrap, .assign_add_wrap, .assign_sub_wrap, .assign_mul_sat, .assign_add_sat, .assign_sub_sat => {
                const lhs = tree.nodeData(node).node_and_node[0];
                if (tree.nodeTag(lhs) == .identifier) {
                    const token = tree.nodeMainToken(lhs);
                    const name = tree.tokenSlice(token);
                    // The discard identifier is syntax, not an unresolved cell.
                    if (std.mem.eql(u8, name, "_")) return null;
                    if (self.bindings.findAt(name, token)) |binding| {
                        const body = tokens.bodyOf(tree, self.fn_decl).?;
                        if (binding.name_token >= tree.firstToken(body) and
                            binding.name_token <= tree.lastToken(body) and
                            binding.origin != .param and binding.origin != .loop_capture and
                            !binding.is_const) return null;
                    }
                }
                return .{ .write = .{
                    .node = node,
                    .target = lhs,
                    .value = tree.nodeData(node).node_and_node[1],
                } };
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                for (read_intrinsics) |intrinsic| {
                    if (std.mem.eql(u8, name, intrinsic)) return null;
                }
                return .{ .write_or_unknown = node };
            },
            .assign_destructure, .@"asm", .asm_simple, .asm_input, .asm_output, .@"suspend", .@"resume", .@"nosuspend", .test_decl => return .{ .write_or_unknown = node },
            .bool_not, .negation, .bit_not, .negation_wrap, .address_of, .@"try", .optional_type, .deref, .@"comptime", .@"defer", .@"return", .@"errdefer", .@"catch", .equal_equal, .bang_equal, .less_than, .greater_than, .less_or_equal, .greater_or_equal, .merge_error_sets, .mul, .div, .mod, .mul_wrap, .mul_sat, .add, .sub, .array_cat, .array_mult, .add_wrap, .sub_wrap, .add_sat, .sub_sat, .shl, .shl_sat, .shr, .bit_and, .bit_xor, .bit_or, .@"orelse", .bool_and, .bool_or, .array_type, .array_access, .array_init_one, .array_init_one_comma, .switch_range, .fn_decl, .fn_proto, .fn_proto_one, .fn_proto_multi, .fn_proto_simple, .container_field_align, .error_union, .struct_init_one, .struct_init_one_comma, .container_field_init, .for_range, .array_init_dot_two, .array_init_dot_two_comma, .struct_init_dot_two, .struct_init_dot_two_comma, .block_two, .block_two_semicolon, .container_decl_two, .container_decl_two_trailing, .tagged_union_two, .tagged_union_two_trailing, .field_access, .unwrap_optional, .grouped_expression, .anyframe_type, .@"break", .@"continue", .array_init_dot, .array_init_dot_comma, .struct_init_dot, .struct_init_dot_comma, .container_decl, .container_decl_trailing, .tagged_union, .tagged_union_trailing, .block, .block_semicolon, .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl, .array_type_sentinel, .ptr_type_aligned, .ptr_type_sentinel, .ptr_type, .ptr_type_bit_range, .slice_open, .slice, .slice_sentinel, .array_init, .array_init_comma, .struct_init, .struct_init_comma, .container_decl_arg, .container_decl_arg_trailing, .tagged_union_enum_tag, .tagged_union_enum_tag_trailing, .switch_case_one, .switch_case_inline_one, .switch_case, .switch_case_inline, .while_simple, .while_cont, .@"while", .for_simple, .@"for", .@"if", .if_simple, .container_field, .anyframe_literal, .char_literal, .number_literal, .unreachable_literal, .identifier, .enum_literal, .string_literal, .multiline_string_literal, .error_set_decl, .error_value => return null,
            else => {
                if (tree.fullSwitch(node) != null) return null;
                return .{ .write_or_unknown = node };
            },
        }
    }

    fn exhausted(self: *const Scan, node: Ast.Node.Index, limit: budget_mod.Limit, cap: u32) budget_mod.BudgetError {
        const byte = self.tree.tokenStart(self.tree.nodeMainToken(node));
        const position = budget_mod.lineCol(self.tree.source, byte);
        var name: budget_mod.NameBuf = .{};
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(self.tree, &buffer, self.fn_decl)) |proto| {
            if (proto.name_token) |token| name.set(self.tree.tokenSlice(token));
        }
        return budget_mod.fail(.{
            .limit = limit,
            .limit_value = cap,
            .reached = cap,
            .byte = byte,
            .line = position.line,
            .column = position.column,
            .function = name,
        });
    }
};

// Compiler intrinsic semantics only; ordinary callee spellings never occur here.
// In particular memory writes, atomics, imports and unknown builtins fail closed.
const read_intrinsics = [_][]const u8{
    "@as",           "@bitCast",         "@intCast",         "@floatCast",              "@ptrCast",         "@alignCast",
    "@constCast",    "@volatileCast",    "@addrSpaceCast",   "@truncate",               "@intFromPtr",      "@ptrFromInt",
    "@intFromEnum",  "@enumFromInt",     "@intFromBool",     "@floatFromInt",           "@intFromFloat",    "@errorCast",
    "@errorFromInt", "@intFromError",    "@errorName",       "@TypeOf",                 "@typeInfo",        "@sizeOf",
    "@alignOf",      "@bitSizeOf",       "@offsetOf",        "@bitOffsetOf",            "@typeName",        "@tagName",
    "@hasField",     "@hasDecl",         "@FieldType",       "@field",                  "@Int",             "@min",
    "@max",          "@abs",             "@clz",             "@ctz",                    "@popCount",        "@byteSwap",
    "@bitReverse",   "@addWithOverflow", "@subWithOverflow", "@mulWithOverflow",        "@shlWithOverflow", "@divExact",
    "@divFloor",     "@divTrunc",        "@mod",             "@rem",                    "@sqrt",            "@sin",
    "@cos",          "@tan",             "@exp",             "@exp2",                   "@log",             "@log2",
    "@log10",        "@floor",           "@ceil",            "@trunc",                  "@round",           "@mulAdd",
    "@splat",        "@shuffle",         "@select",          "@reduce",                 "@Vector",          "@branchHint",
    "@compileError", "@compileLog",      "@returnAddress",   "@disableInstrumentation",
};

test "closed scan retains exact indexed store target and written value" {
    const source: [:0]const u8 =
        \\fn replace(values: []u32, index: usize) void { values[index] = 7; }
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    const declaration = tree.rootDecls()[0];
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(&tree, &buffer, declaration).?;
    const body = tokens.bodyOf(&tree, declaration).?;
    var bindings = try @import("../model/local_bindings.zig").build(gpa, &tree, proto, body);
    defer bindings.deinit();
    var scan = Scan.init(&tree, declaration, &bindings);
    var writes: usize = 0;
    while (try scan.next()) |event| {
        switch (event) {
            .write => |write| {
                writes += 1;
                try std.testing.expectEqual(Ast.Node.Tag.array_access, tree.nodeTag(write.target));
                try std.testing.expectEqualStrings("values", tree.tokenSlice(tree.firstToken(write.target)));
                try std.testing.expectEqualStrings("7", tree.tokenSlice(tree.nodeMainToken(write.value)));
            },
            .write_or_unknown => return error.UnexpectedOpaqueEffect,
            .node, .call => {},
        }
    }
    try std.testing.expectEqual(@as(usize, 1), writes);
}

test "compiler hints and return address reads preserve closed storage effect scanning" {
    const source: [:0]const u8 =
        \\fn peek(values: []const u8) u8 { @branchHint(.cold); _ = @returnAddress(); return values[0]; }
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    const declaration = tree.rootDecls()[0];
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(&tree, &buffer, declaration).?;
    const body = tokens.bodyOf(&tree, declaration).?;
    var bindings = try @import("../model/local_bindings.zig").build(gpa, &tree, proto, body);
    defer bindings.deinit();
    var scan = Scan.init(&tree, declaration, &bindings);
    var saw_hint = false;
    var saw_address = false;
    while (try scan.next()) |event| {
        switch (event) {
            .node => |node| {
                if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@branchHint"))
                    saw_hint = true;
                if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@returnAddress"))
                    saw_address = true;
            },
            .write, .write_or_unknown => return error.UnexpectedStorageEffect,
            .call => return error.UnexpectedCall,
        }
    }
    try std.testing.expect(saw_hint);
    try std.testing.expect(saw_address);
}

test "comptime diagnostics do not become runtime storage writes" {
    const source: [:0]const u8 =
        \\fn peek(comptime T: type, values: []const T) T {
        \\    if (@sizeOf(T) == 0) @compileError("empty element type");
        \\    comptime { @compileLog(@tagName(@as(enum { normal }, .normal)), @typeName(T)); }
        \\    return values[0];
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    const declaration = tree.rootDecls()[0];
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(&tree, &buffer, declaration).?;
    const body = tokens.bodyOf(&tree, declaration).?;
    var bindings = try @import("../model/local_bindings.zig").build(gpa, &tree, proto, body);
    defer bindings.deinit();
    var scan = Scan.init(&tree, declaration, &bindings);
    var saw_error = false;
    var saw_log = false;
    var saw_tag = false;
    while (try scan.next()) |event| {
        switch (event) {
            .node => |node| {
                const token = tree.tokenSlice(tree.nodeMainToken(node));
                saw_error = saw_error or std.mem.eql(u8, token, "@compileError");
                saw_log = saw_log or std.mem.eql(u8, token, "@compileLog");
                saw_tag = saw_tag or std.mem.eql(u8, token, "@tagName");
            },
            .write, .write_or_unknown => return error.UnexpectedStorageEffect,
            .call => return error.UnexpectedCall,
        }
    }
    try std.testing.expect(saw_error);
    try std.testing.expect(saw_log);
    try std.testing.expect(saw_tag);
}
