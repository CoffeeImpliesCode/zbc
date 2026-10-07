//! Stores all Scopes and Declarations/Symbols inside a Zig source file.

const std = @import("std");
const ast = @import("ast.zig");
const Ast = std.zig.Ast;
const tracy = @import("tracy_stub.zig");
const offsets = @import("offsets.zig");

const DocumentScope = @This();

scopes: std.MultiArrayList(Scope),
declarations: std.MultiArrayList(Declaration),
/// used for looking up a child declaration in a given scope
declaration_lookup_map: DeclarationLookupMap,
extra: std.ArrayList(u32),

/// Every `index` inside this `ArrayhashMap` is equivalent to a `Declaration.Index`
/// This means that every declaration is only the child of a single scope
pub const DeclarationLookupMap = std.array_hash_map.Custom(
    DeclarationLookup,
    void,
    DeclarationLookupContext,
    false,
);

pub const DeclarationLookup = struct {
    pub const Kind = enum { field, other, label };
    scope: Scope.Index,
    name: []const u8,
    kind: Kind,
};

pub const DeclarationLookupContext = struct {
    pub fn hash(self: @This(), s: DeclarationLookup) u32 {
        _ = self;
        var hasher: std.hash.Wyhash = .init(0);
        std.hash.autoHash(&hasher, s.scope);
        hasher.update(s.name);
        std.hash.autoHash(&hasher, s.kind);
        return @truncate(hasher.final());
    }

    pub fn eql(self: @This(), a: DeclarationLookup, b: DeclarationLookup, b_index: usize) bool {
        _ = self;
        _ = b_index;
        return a.scope == b.scope and a.kind == b.kind and std.mem.eql(u8, a.name, b.name);
    }
};

pub const Declaration = union(enum) {
    /// Index of the ast node.
    /// Can have one of the following tags:
    ///   - `.container_field`
    ///   - `.fn_proto`
    ///   - `.fn_decl`
    ///   - `.var_decl`
    ast_node: Ast.Node.Index,
    /// Function parameter
    function_parameter: Param,
    /// - `if (condition) |identifier| {}`
    /// - `while (condition) |identifier| {}`
    optional_payload: struct {
        identifier: Ast.TokenIndex,
        condition: Ast.Node.Index,
    },
    /// - `for (condition) |identifier| {}`
    /// - `for (..., condition, ...) |..., identifier, ...| {}`
    for_loop_payload: struct {
        identifier: Ast.TokenIndex,
        condition: Ast.Node.Index,
    },
    /// - `if (condition) |identifier| {} else |_| {}`
    /// - `while (condition) |identifier| {} else |_| {}`
    error_union_payload: struct {
        identifier: Ast.TokenIndex,
        condition: Ast.Node.Index,
    },
    /// - `if (condition) |_| {} else |identifier| {}`
    /// - `while (condition) |_| {} else |identifier| {}`
    /// - `condition catch |identifier| {}`
    /// - `errdefer |identifier| {}` (condition is `.none`)
    error_union_error: struct {
        identifier: Ast.TokenIndex,
        condition: Ast.Node.OptionalIndex,
    },
    assign_destructure: AssignDestructure,
    /// - `switch (condition) { .case => |value| {} }`
    switch_payload: Switch,
    /// - `switch (condition) { inline .case => |_, tag| {} }`
    /// - `switch (condition) { inline else => |_, tag| {} }`
    switch_inline_tag_payload: Switch,
    label: struct {
        identifier: Ast.TokenIndex,
        block: Ast.Node.Index,
    },
    /// always an identifier
    /// used as child declarations of an error set declaration
    error_token: Ast.TokenIndex,

    comptime {
        for (@typeInfo(Declaration).@"union".fields) |field| {
            std.debug.assert(@sizeOf(field.type) <= 8);
        }
    }

    pub const Param = struct {
        param_index: u16,
        func: Ast.Node.Index,

        pub fn get(self: Param, tree: *const Ast) ?Ast.full.FnProto.Param {
            var buffer: [1]Ast.Node.Index = undefined;
            const func = tree.fullFnProto(&buffer, self.func).?;
            var param_index: u16 = 0;
            var it: ast.FnParamIterator = .init(&func, tree);
            while (it.next()) |param| : (param_index += 1) {
                if (self.param_index == param_index) return param;
            }
            return null;
        }
    };

    pub const AssignDestructure = struct {
        /// tag is .assign_destructure
        node: Ast.Node.Index,
        index: u32,

        pub fn getVarDeclNode(self: AssignDestructure, tree: *const Ast) Ast.Node.Index {
            const extra_index = tree.nodeData(self.node).extra_and_node[0];
            return @enumFromInt(tree.extra_data[@intFromEnum(extra_index) + 1 ..][self.index]);
        }

        pub fn getFullVarDecl(self: AssignDestructure, tree: *const Ast) Ast.full.VarDecl {
            return tree.fullVarDecl(self.getVarDeclNode(tree)).?;
        }
    };

    pub const Switch = struct {
        /// tag is `.@"switch"` or `.switch_comma`
        node: Ast.Node.Index,
        /// is guaranteed to have a payload_token
        case_index: u32,

        pub fn getCase(self: Switch, tree: *const Ast) Ast.full.SwitchCase {
            const extra_index = tree.nodeData(self.node).node_and_extra[1];
            const cases = tree.extraDataSlice(tree.extraData(extra_index, Ast.Node.SubRange), Ast.Node.Index);
            return tree.fullSwitchCase(cases[self.case_index]).?;
        }
    };

    pub const Index = enum(u32) {
        _,

        pub fn toOptional(index: Index) OptionalIndex {
            return @enumFromInt(@intFromEnum(index));
        }
    };

    pub const OptionalIndex = enum(u32) {
        none = std.math.maxInt(u32),
        _,

        pub fn unwrap(index: OptionalIndex) ?Index {
            if (index == .none) return null;
            return @enumFromInt(@intFromEnum(index));
        }
    };

    pub fn eql(a: Declaration, b: Declaration) bool {
        return std.meta.eql(a, b);
    }

    /// Returns a `.identifier` or `.builtin` token.
    pub fn nameToken(decl: Declaration, tree: *const Ast) Ast.TokenIndex {
        return switch (decl) {
            .ast_node => |node| {
                var buffer: [1]Ast.Node.Index = undefined;
                const token_index = switch (tree.nodeTag(node)) {
                    .local_var_decl,
                    .global_var_decl,
                    .simple_var_decl,
                    .aligned_var_decl,
                    => tree.nodeMainToken(node) + 1,
                    .fn_proto,
                    .fn_proto_multi,
                    .fn_proto_one,
                    .fn_proto_simple,
                    .fn_decl,
                    => tree.fullFnProto(&buffer, node).?.name_token.?,

                    .container_field,
                    .container_field_init,
                    .container_field_align,
                    => tree.nodeMainToken(node),

                    else => unreachable,
                };

                switch (tree.tokenTag(token_index)) {
                    .identifier, .builtin => return token_index,
                    else => unreachable,
                }
            },
            .function_parameter => |payload| payload.get(tree).?.name_token.?,
            .optional_payload => |payload| payload.identifier,
            .error_union_payload => |payload| payload.identifier,
            .error_union_error => |payload| payload.identifier,
            .for_loop_payload => |payload| payload.identifier,
            .label => |payload| payload.identifier,
            .error_token => |error_token| error_token,
            .assign_destructure => |payload| {
                const var_decl_node = payload.getVarDeclNode(tree);
                const varDecl = tree.fullVarDecl(var_decl_node).?;
                return varDecl.ast.mut_token + 1;
            },
            .switch_payload,
            .switch_inline_tag_payload,
            => |payload| {
                const case = payload.getCase(tree);
                const payload_token = case.payload_token.?;
                return payload_token + @intFromBool(tree.tokenTag(payload_token) == .asterisk) + @as(Ast.TokenIndex, 2) * @intFromBool(decl == .switch_inline_tag_payload);
            },
        };
    }
};

pub const Scope = struct {
    pub const Tag = enum(u3) {
        /// `tree.nodeTag(ast_node)` is ContainerDecl or Root or ErrorSetDecl
        container,
        /// `tree.nodeTag(ast_node)` is FnProto
        function,
        /// `tree.nodeTag(ast_node)` is Block
        block,
        other,

        pub fn isContainer(self: @This()) bool {
            return switch (self) {
                .container => true,
                .block, .function, .other => false,
            };
        }
    };

    pub const Data = packed union {
        ast_node: Ast.Node.Index,
    };

    pub const SmallLoc = packed struct {
        start: u32,
        end: u32,
    };

    pub const ChildScopes = union {
        pub const small_size = 4;

        small: [small_size]Scope.OptionalIndex,
        other: struct {
            start: u32,
            end: u32,
        },
    };

    pub const ChildDeclarations = union {
        pub const small_size = 2;

        small: [small_size]Declaration.OptionalIndex,
        other: struct {
            start: u32,
            end: u32,
        },
    };

    data: packed struct(u64) {
        tag: Tag,
        is_child_scopes_small: bool,
        is_child_decls_small: bool,
        _: u27 = undefined,
        data: Data,
    },
    // offsets.Loc store `usize` instead of `u32`
    // zig only allows files up to `std.math.maxInt(u32)` bytes to do this kind of optimization.
    loc: SmallLoc,
    parent_scope: OptionalIndex,
    // child scopes have contiguous indices
    // used only by the `EnclosingScopeIterator`
    child_scopes: ChildScopes,
    child_declarations: ChildDeclarations,

    pub const Index = enum(u32) {
        root,
        _,

        pub fn toOptional(index: Index) OptionalIndex {
            return @enumFromInt(@intFromEnum(index));
        }
    };

    pub const OptionalIndex = enum(u32) {
        root,
        none = std.math.maxInt(u32),
        _,

        pub fn unwrap(index: OptionalIndex) ?Index {
            if (index == .none) return null;
            return @enumFromInt(@intFromEnum(index));
        }
    };
};

const ScopeContext = struct {
    allocator: std.mem.Allocator,
    tree: *const Ast,
    doc_scope: *DocumentScope,

    current_scope: Scope.OptionalIndex = .none,
    child_scopes_scratch: std.ArrayList(Scope.Index) = .empty,
    child_declarations_scratch: std.ArrayList(Declaration.Index) = .empty,

    fn deinit(context: *ScopeContext) void {
        context.child_scopes_scratch.deinit(context.allocator);
        context.child_declarations_scratch.deinit(context.allocator);
    }

    const PushedScope = struct {
        context: *ScopeContext,

        scope: Scope.Index,

        scopes_start: u32,
        declarations_start: u32,

        fn pushDeclaration(
            pushed: PushedScope,
            identifier_token: Ast.TokenIndex,
            declaration: Declaration,
            kind: DeclarationLookup.Kind,
        ) error{OutOfMemory}!void {
            std.debug.assert((declaration == .label) == (kind == .label));
            const name = offsets.identifierTokenToNameSlice(pushed.context.tree, identifier_token);
            if (std.mem.eql(u8, name, "_")) return;
            defer std.debug.assert(pushed.context.doc_scope.declarations.len == pushed.context.doc_scope.declaration_lookup_map.count());

            if (@import("builtin").mode == .Debug) {
                // Check that nameToken works
                std.debug.assert(identifier_token == declaration.nameToken(pushed.context.tree));
            }

            const context = pushed.context;
            const doc_scope = context.doc_scope;
            const allocator = context.allocator;

            const gop = try doc_scope.declaration_lookup_map.getOrPut(allocator, .{
                .scope = pushed.scope,
                .name = name,
                .kind = kind,
            });
            if (gop.found_existing) return;
            errdefer doc_scope.declaration_lookup_map.swapRemoveAt(gop.index);

            try doc_scope.declarations.append(allocator, declaration);
            errdefer _ = doc_scope.declarations.pop();
            const declaration_index: Declaration.Index = @enumFromInt(doc_scope.declarations.len - 1);

            const data = &doc_scope.scopes.items(.data)[@intFromEnum(pushed.scope)];
            const child_declarations = &doc_scope.scopes.items(.child_declarations)[@intFromEnum(pushed.scope)];

            if (!data.is_child_decls_small) {
                try context.child_declarations_scratch.append(allocator, declaration_index);
                return;
            }

            for (&child_declarations.small) |*scd| {
                if (scd.* == .none) {
                    scd.* = declaration_index.toOptional();
                    break;
                }
            } else {
                try context.child_declarations_scratch.ensureUnusedCapacity(allocator, Scope.ChildDeclarations.small_size + 1);
                data.is_child_decls_small = false;
                context.child_declarations_scratch.appendSliceAssumeCapacity(@ptrCast(&child_declarations.small));
                context.child_declarations_scratch.appendAssumeCapacity(declaration_index);
            }
        }

        fn finalize(pushed: PushedScope) error{OutOfMemory}!void {
            const context = pushed.context;
            const allocator = context.allocator;

            const slice = context.doc_scope.scopes.slice();
            const data = slice.items(.data)[@intFromEnum(pushed.scope)];

            if (!data.is_child_decls_small) {
                const declaration_start = context.doc_scope.extra.items.len;
                try context.doc_scope.extra.appendSlice(allocator, @ptrCast(context.child_declarations_scratch.items[pushed.declarations_start..]));
                const declaration_end = context.doc_scope.extra.items.len;
                context.child_declarations_scratch.items.len = pushed.declarations_start;

                slice.items(.child_declarations)[@intFromEnum(pushed.scope)] = .{
                    .other = .{
                        .start = @intCast(declaration_start),
                        .end = @intCast(declaration_end),
                    },
                };
            }

            if (!data.is_child_scopes_small) {
                const scope_start = context.doc_scope.extra.items.len;
                try context.doc_scope.extra.appendSlice(allocator, @ptrCast(context.child_scopes_scratch.items[pushed.scopes_start..]));
                const scope_end = context.doc_scope.extra.items.len;
                context.child_scopes_scratch.items.len = pushed.scopes_start;

                slice.items(.child_scopes)[@intFromEnum(pushed.scope)] = .{
                    .other = .{
                        .start = @intCast(scope_start),
                        .end = @intCast(scope_end),
                    },
                };
            }

            std.debug.assert(context.current_scope.unwrap().? == pushed.scope);
            context.current_scope = context.doc_scope.getScopeParent(pushed.scope);

            std.debug.assert(context.doc_scope.declarations.len == context.doc_scope.declaration_lookup_map.count());
        }
    };

    fn startScope(context: *ScopeContext, tag: Scope.Tag, data: Scope.Data, loc: Scope.SmallLoc) error{OutOfMemory}!PushedScope {
        // Registering this scope with its parent may append to the shared
        // child-scope scratch list. Its own offset starts after that append.
        // Both recorded offsets must remain addressable as u32.
        const declarations_start = std.math.cast(u32, context.child_declarations_scratch.items.len) orelse return error.OutOfMemory;

        try context.doc_scope.scopes.append(context.allocator, .{
            .data = .{
                .tag = tag,
                .is_child_scopes_small = true,
                .is_child_decls_small = true,
                .data = data,
            },
            .loc = loc,
            .parent_scope = context.current_scope,
            .child_scopes = .{
                .small = @splat(.none),
            },
            .child_declarations = .{
                .small = @splat(.none),
            },
        });
        const new_scope_index: Scope.Index = @enumFromInt(context.doc_scope.scopes.len - 1);
        if (context.current_scope.unwrap()) |parent_scope| {
            try context.pushChildScope(parent_scope, new_scope_index);
        }
        const scopes_start = std.math.cast(u32, context.child_scopes_scratch.items.len) orelse return error.OutOfMemory;

        context.current_scope = new_scope_index.toOptional();
        return .{
            .context = context,
            .scope = context.current_scope.unwrap().?,
            .scopes_start = scopes_start,
            .declarations_start = declarations_start,
        };
    }

    fn pushChildScope(
        context: *ScopeContext,
        scope_index: Scope.Index,
        child_scope_index: Scope.Index,
    ) error{OutOfMemory}!void {
        const doc_scope = context.doc_scope;
        const allocator = context.allocator;

        const data = &doc_scope.scopes.items(.data)[@intFromEnum(scope_index)];
        const child_scopes = &doc_scope.scopes.items(.child_scopes)[@intFromEnum(scope_index)];

        if (!data.is_child_scopes_small) {
            try context.child_scopes_scratch.append(allocator, child_scope_index);
            return;
        }

        for (&child_scopes.small) |*scd| {
            if (scd.* == .none) {
                scd.* = child_scope_index.toOptional();
                break;
            }
        } else {
            data.is_child_scopes_small = false;

            try context.child_scopes_scratch.ensureUnusedCapacity(allocator, Scope.ChildScopes.small_size + 1);
            context.child_scopes_scratch.appendSliceAssumeCapacity(@ptrCast(&child_scopes.small));
            context.child_scopes_scratch.appendAssumeCapacity(child_scope_index);
        }
    }
};

pub fn init(allocator: std.mem.Allocator, tree: *const Ast) error{OutOfMemory}!DocumentScope {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    var document_scope: DocumentScope = .{
        .scopes = .empty,
        .declarations = .empty,
        .declaration_lookup_map = .empty,
        .extra = .empty,
    };
    errdefer document_scope.deinit(allocator);

    var context: ScopeContext = .{
        .allocator = allocator,
        .tree = tree,
        .doc_scope = &document_scope,
    };
    defer context.deinit();
    switch (tree.mode) {
        .zig => try walkContainerDecl(&context, tree, .root),
        .zon => {
            const root_node = tree.nodeData(.root).node;
            // `Scope.SmallLoc` ends are `u32`, so the root scope that spans
            // the whole source can only be started while that source is
            // addressable as one - the same bound `startScope` applies to the
            // scratch offsets it records, and the same bound
            // `Handle.requireAddressableSource` applies before a document is
            // stored.  A source that does not fit is refused here rather
            // than truncated into a scope that would report wrong positions.
            const source_end = std.math.cast(u32, tree.source.len) orelse return error.OutOfMemory;
            const new_scope = try context.startScope(
                .container,
                .{ .ast_node = root_node },
                .{ .start = 0, .end = source_end },
            );
            try walkNode(&context, tree, root_node);
            try new_scope.finalize();
        },
    }

    return document_scope;
}

pub fn deinit(scope: *DocumentScope, allocator: std.mem.Allocator) void {
    scope.scopes.deinit(allocator);
    scope.declarations.deinit(allocator);
    scope.declaration_lookup_map.deinit(allocator);
    scope.extra.deinit(allocator);
}

fn locToSmallLoc(loc: offsets.Loc) Scope.SmallLoc {
    return .{
        .start = @intCast(loc.start),
        .end = @intCast(loc.end),
    };
}

/// Similar to `walkNode` but also returns a new scope.
/// Asserts that `node_idx != .root`
/// Caller must finalize the scope
fn walkNodeEnsureScope(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
    start_token: Ast.TokenIndex,
) error{OutOfMemory}!ScopeContext.PushedScope {
    std.debug.assert(node_idx != .root);
    switch (tree.nodeTag(node_idx)) {
        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        => {
            // special case where we reuse the block scope
            return try walkBlockNodeKeepOpen(context, tree, node_idx, start_token);
        },
        else => {
            const new_scope = try context.startScope(
                .other,
                undefined,
                locToSmallLoc(offsets.tokensToLoc(tree, start_token, ast.lastToken(tree, node_idx))),
            );
            try walkNode(context, tree, node_idx);
            return new_scope;
        },
    }
}

fn walkNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const tag = tree.nodeTag(node_idx);
    try switch (tag) {
        .root => return,
        .container_decl,
        .container_decl_trailing,
        .container_decl_arg,
        .container_decl_arg_trailing,
        .container_decl_two,
        .container_decl_two_trailing,
        .tagged_union,
        .tagged_union_trailing,
        .tagged_union_two,
        .tagged_union_two_trailing,
        .tagged_union_enum_tag,
        .tagged_union_enum_tag_trailing,
        => walkContainerDecl(context, tree, node_idx),
        .error_set_decl => walkErrorSetNode(context, tree, node_idx),
        .fn_proto,
        .fn_proto_one,
        .fn_proto_simple,
        .fn_proto_multi,
        .fn_decl,
        => walkFuncNode(context, tree, node_idx),
        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        => walkBlockNode(context, tree, node_idx),
        .@"if",
        .if_simple,
        => walkIfNode(context, tree, node_idx),
        .@"catch" => walkCatchNode(context, tree, node_idx),
        .@"while",
        .while_simple,
        .while_cont,
        => walkWhileNode(context, tree, node_idx),
        .@"for",
        .for_simple,
        => walkForNode(context, tree, node_idx),
        .@"switch",
        .switch_comma,
        => walkSwitchNode(context, tree, node_idx),

        .@"errdefer" => walkErrdeferNode(context, tree, node_idx),
        .@"defer",
        .bool_not,
        .negation,
        .bit_not,
        .negation_wrap,
        .address_of,
        .@"try",
        .optional_type,
        .deref,
        .@"suspend",
        .@"resume",
        .@"comptime",
        .@"nosuspend",
        => walkUnaryOpNode(context, tree, node_idx),

        .equal_equal,
        .bang_equal,
        .less_than,
        .greater_than,
        .less_or_equal,
        .greater_or_equal,
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_add,
        .assign_sub,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_and,
        .assign_bit_xor,
        .assign_bit_or,
        .assign_mul_wrap,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        .assign,
        .merge_error_sets,
        .mul,
        .div,
        .mod,
        .mul_wrap,
        .mul_sat,
        .add,
        .sub,
        .array_cat,
        .array_mult,
        .add_wrap,
        .sub_wrap,
        .add_sat,
        .sub_sat,
        .shl,
        .shl_sat,
        .shr,
        .bit_and,
        .bit_xor,
        .bit_or,
        .@"orelse",
        .bool_and,
        .bool_or,
        .array_type,
        .array_access,
        .array_init_one,
        .array_init_one_comma,
        .switch_range,
        .error_union,
        .container_field_align,
        => walkBinOpNode(context, tree, node_idx),

        .array_init_dot_two,
        .array_init_dot_two_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => walkOptNodeAndOptNode(context, tree, node_idx),

        .struct_init_one,
        .struct_init_one_comma,
        .call_one,
        .call_one_comma,
        .switch_case_one,
        .switch_case_inline_one,
        .container_field_init,
        .for_range,
        => walkNodeAndOptNode(context, tree, node_idx),

        .global_var_decl,
        .local_var_decl,
        .simple_var_decl,
        .aligned_var_decl,
        .assign_destructure,
        .array_type_sentinel,
        .ptr_type_aligned,
        .ptr_type_sentinel,
        .ptr_type,
        .ptr_type_bit_range,
        .slice_open,
        .slice,
        .slice_sentinel,
        .array_init_dot,
        .array_init_dot_comma,
        .array_init,
        .array_init_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init,
        .struct_init_comma,
        .call,
        .call_comma,
        .switch_case,
        .switch_case_inline,
        .builtin_call,
        .builtin_call_comma,
        .container_field,
        .asm_simple,
        .@"asm",

        .grouped_expression,
        .field_access,
        .unwrap_optional,
        .@"return",
        .test_decl,
        .@"break",
        .anyframe_type,
        => walkOtherNode(context, tree, node_idx),

        .asm_output,
        .asm_input,
        => unreachable,

        .@"continue",
        .anyframe_literal,
        .char_literal,
        .number_literal,
        .unreachable_literal,
        .identifier,
        .enum_literal,
        .string_literal,
        .multiline_string_literal,
        .error_value,
        => return,
    };
}

noinline fn walkContainerDecl(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    var buf: [2]Ast.Node.Index = undefined;
    const container_decl = tree.fullContainerDecl(&buf, node_idx).?;

    const scope = try context.startScope(
        .container,
        .{ .ast_node = node_idx },
        locToSmallLoc(offsets.nodeToLoc(tree, node_idx)),
    );

    for (container_decl.ast.members) |decl| {
        try walkNode(context, tree, decl);

        switch (tree.nodeTag(decl)) {
            .test_decl,
            .@"comptime",
            => continue,

            .container_field,
            .container_field_init,
            .container_field_align,
            => {
                var container_field = tree.fullContainerField(decl).?;

                const is_struct = node_idx == .root or tree.tokenTag(container_decl.ast.main_token) == .keyword_struct;
                if (is_struct and container_field.ast.tuple_like) continue;

                container_field.convertToNonTupleLike(tree);
                if (container_field.ast.tuple_like) continue;
                const main_token = container_field.ast.main_token;
                if (tree.tokenTag(main_token) != .identifier) continue;
                try scope.pushDeclaration(main_token, .{ .ast_node = decl }, .field);
            },
            .fn_proto,
            .fn_proto_multi,
            .fn_proto_one,
            .fn_proto_simple,
            .fn_decl,
            => {
                var buffer: [1]Ast.Node.Index = undefined;
                const name_token = tree.fullFnProto(&buffer, decl).?.name_token orelse continue;
                try scope.pushDeclaration(name_token, .{ .ast_node = decl }, .other);
            },
            .local_var_decl,
            .global_var_decl,
            .simple_var_decl,
            .aligned_var_decl,
            => {
                const name_token = tree.fullVarDecl(decl).?.ast.mut_token + 1;
                try scope.pushDeclaration(name_token, .{ .ast_node = decl }, .other);
            },

            else => unreachable,
        }
    }

    try scope.finalize();
}

noinline fn walkErrorSetNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const scope = try context.startScope(
        .container,
        .{ .ast_node = node_idx },
        locToSmallLoc(offsets.nodeToLoc(tree, node_idx)),
    );

    const lbrace, const rbrace = tree.nodeData(node_idx).token_and_token;
    for (lbrace + 1..rbrace) |tok_i| {
        if (tree.tokenTag(@intCast(tok_i)) != .identifier) continue;
        const identifier_token: Ast.TokenIndex = @intCast(tok_i);

        try scope.pushDeclaration(identifier_token, .{ .error_token = identifier_token }, .other);
    }

    try scope.finalize();
}

noinline fn walkFuncNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    var buf: [1]Ast.Node.Index = undefined;
    const func = tree.fullFnProto(&buf, node_idx).?;

    const scope = try context.startScope(
        .function,
        .{ .ast_node = node_idx },
        locToSmallLoc(offsets.nodeToLoc(tree, node_idx)),
    );

    var param_index: u16 = 0;
    var it: ast.FnParamIterator = .init(&func, tree);
    while (it.next()) |param| : (param_index += 1) {
        if (param.name_token) |name_token| {
            try scope.pushDeclaration(
                name_token,
                .{ .function_parameter = .{ .param_index = param_index, .func = node_idx } },
                .other,
            );
        }
        if (param.type_expr) |type_expr| {
            try walkNode(context, tree, type_expr);
        }
    }

    if (func.ast.return_type.unwrap()) |return_type| {
        try walkNode(context, tree, return_type);
    }

    if (tree.nodeTag(node_idx) == .fn_decl) {
        // Visit the function body
        try walkNode(context, tree, tree.nodeData(node_idx).node_and_node[1]);
    }

    try scope.finalize();
}

noinline fn walkBlockNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const pushed_scope = try walkBlockNodeKeepOpen(context, tree, node_idx, tree.firstToken(node_idx));
    try pushed_scope.finalize();
}

fn walkBlockNodeKeepOpen(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
    start_token: Ast.TokenIndex,
) error{OutOfMemory}!ScopeContext.PushedScope {
    const last_token = ast.lastToken(tree, node_idx);

    const scope = try context.startScope(
        .block,
        .{ .ast_node = node_idx },
        locToSmallLoc(offsets.tokensToLoc(tree, start_token, last_token)),
    );

    if (ast.blockLabel(tree, node_idx)) |label_token| {
        try scope.pushDeclaration(
            label_token,
            .{ .label = .{ .identifier = label_token, .block = node_idx } },
            .label,
        );
    }

    var buffer: [2]Ast.Node.Index = undefined;
    const statements = tree.blockStatements(&buffer, node_idx).?;

    for (statements) |idx| {
        try walkNode(context, tree, idx);
        switch (tree.nodeTag(idx)) {
            .global_var_decl,
            .local_var_decl,
            .aligned_var_decl,
            .simple_var_decl,
            => {
                const var_decl = tree.fullVarDecl(idx).?;
                const name_token = var_decl.ast.mut_token + 1;
                try scope.pushDeclaration(name_token, .{ .ast_node = idx }, .other);
            },
            .assign_destructure => {
                const assign_destructure = tree.assignDestructure(idx);

                for (assign_destructure.ast.variables, 0..) |lhs_node, i| {
                    const var_decl = tree.fullVarDecl(lhs_node) orelse continue;
                    const name_token = var_decl.ast.mut_token + 1;
                    try scope.pushDeclaration(
                        name_token,
                        .{ .assign_destructure = .{ .node = idx, .index = @intCast(i) } },
                        .other,
                    );
                }
            },
            else => continue,
        }
    }

    return scope;
}

noinline fn walkIfNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const if_node = ast.fullIf(tree, node_idx).?;

    try walkNode(context, tree, if_node.ast.cond_expr);

    if (if_node.payload_token) |payload_token| {
        const name_token = payload_token + @intFromBool(tree.tokenTag(payload_token) == .asterisk);

        const decl: Declaration = if (if_node.error_token != null)
            .{ .error_union_payload = .{ .identifier = name_token, .condition = if_node.ast.cond_expr } }
        else
            .{ .optional_payload = .{ .identifier = name_token, .condition = if_node.ast.cond_expr } };

        const then_scope = try walkNodeEnsureScope(context, tree, if_node.ast.then_expr, name_token);
        try then_scope.pushDeclaration(name_token, decl, .other);
        try then_scope.finalize();
    } else {
        try walkNode(context, tree, if_node.ast.then_expr);
    }

    if (if_node.ast.else_expr.unwrap()) |else_expr| {
        if (if_node.error_token) |error_token| {
            const else_scope = try walkNodeEnsureScope(context, tree, else_expr, error_token);
            try else_scope.pushDeclaration(
                error_token,
                .{ .error_union_error = .{ .identifier = error_token, .condition = if_node.ast.cond_expr.toOptional() } },
                .other,
            );
            try else_scope.finalize();
        } else {
            try walkNode(context, tree, else_expr);
        }
    }
}

noinline fn walkCatchNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const lhs, const rhs = tree.nodeData(node_idx).node_and_node;
    try walkNode(context, tree, lhs);

    const catch_token = tree.nodeMainToken(node_idx) + 2;
    if (catch_token < tree.tokens.len and
        tree.tokenTag(catch_token - 1) == .pipe and
        tree.tokenTag(catch_token) == .identifier)
    {
        const expr_scope = try walkNodeEnsureScope(context, tree, rhs, catch_token);
        try expr_scope.pushDeclaration(
            catch_token,
            .{ .error_union_error = .{ .identifier = catch_token, .condition = lhs.toOptional() } },
            .other,
        );
        try expr_scope.finalize();
    } else {
        try walkNode(context, tree, rhs);
    }
}

/// errdefer |payload_token|? body
noinline fn walkErrdeferNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const payload_token, const body = tree.nodeData(node_idx).opt_token_and_node;

    if (payload_token.unwrap()) |payload| {
        const name_token = payload + @intFromBool(tree.tokenTag(payload) == .asterisk);

        // The capture takes precedence over every outer binding of that name,
        // but only for the deferred body.  It is an error value without an
        // error union expression behind it, hence the `.none` condition.
        const body_scope = try walkNodeEnsureScope(context, tree, body, name_token);
        try body_scope.pushDeclaration(
            name_token,
            .{ .error_union_error = .{ .identifier = name_token, .condition = .none } },
            .other,
        );
        try body_scope.finalize();
    } else {
        try walkNode(context, tree, body);
    }
}

/// label_token: inline_token while (cond_expr) |payload_token| : (cont_expr) then_expr else |error_token| else_expr
noinline fn walkWhileNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const while_node = ast.fullWhile(tree, node_idx).?;

    try walkNode(context, tree, while_node.ast.cond_expr);

    const payload_declaration, const payload_name_token = if (while_node.payload_token) |payload_token| blk: {
        const name_token = payload_token + @intFromBool(tree.tokenTag(payload_token) == .asterisk);

        const decl: Declaration = if (while_node.error_token != null)
            .{ .error_union_payload = .{ .identifier = name_token, .condition = while_node.ast.cond_expr } }
        else
            .{ .optional_payload = .{ .identifier = name_token, .condition = while_node.ast.cond_expr } };
        break :blk .{ decl, name_token };
    } else .{ null, null };

    if (while_node.ast.cont_expr.unwrap()) |cont_expr| {
        if (payload_declaration) |decl| {
            const cont_scope = try walkNodeEnsureScope(context, tree, cont_expr, tree.firstToken(cont_expr));
            try cont_scope.pushDeclaration(payload_name_token.?, decl, .other);
            try cont_scope.finalize();
        } else {
            try walkNode(context, tree, cont_expr);
        }
    }

    if (payload_declaration != null or while_node.label_token != null) {
        const then_start = while_node.payload_token orelse tree.firstToken(while_node.ast.then_expr);
        const then_scope = try walkNodeEnsureScope(context, tree, while_node.ast.then_expr, then_start);

        if (while_node.label_token) |label| {
            try then_scope.pushDeclaration(
                label,
                .{ .label = .{ .identifier = label, .block = while_node.ast.then_expr } },
                .label,
            );
        }
        if (payload_declaration) |decl| {
            try then_scope.pushDeclaration(payload_name_token.?, decl, .other);
        }

        try then_scope.finalize();
    } else {
        try walkNode(context, tree, while_node.ast.then_expr);
    }

    if (while_node.ast.else_expr.unwrap()) |else_expr| {
        if (while_node.label_token != null or while_node.error_token != null) {
            const else_start = while_node.error_token orelse tree.firstToken(else_expr);
            const else_scope = try walkNodeEnsureScope(context, tree, else_expr, else_start);

            if (while_node.label_token) |label| {
                try else_scope.pushDeclaration(
                    label,
                    .{ .label = .{ .identifier = label, .block = while_node.ast.then_expr } },
                    .label,
                );
            }

            if (while_node.error_token) |error_token| {
                try else_scope.pushDeclaration(
                    error_token,
                    .{ .error_union_error = .{ .identifier = error_token, .condition = while_node.ast.cond_expr.toOptional() } },
                    .other,
                );
            }

            try else_scope.finalize();
        } else {
            try walkNode(context, tree, else_expr);
        }
    }
}

/// label_token: inline_token for (inputs) |capture_tokens| then_expr else else_expr
noinline fn walkForNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const for_node = ast.fullFor(tree, node_idx).?;

    for (for_node.ast.inputs) |input_node| {
        try walkNode(context, tree, input_node);
    }

    const then_scope = try walkNodeEnsureScope(context, tree, for_node.ast.then_expr, for_node.payload_token);

    var capture_token = for_node.payload_token;
    for (for_node.ast.inputs) |input| {
        if (capture_token + 1 >= tree.tokens.len) break;
        const capture_is_ref = tree.tokenTag(capture_token) == .asterisk;
        const name_token = capture_token + @intFromBool(capture_is_ref);
        capture_token = name_token + 2;

        if (tree.tokenTag(name_token) != .identifier) break;
        try then_scope.pushDeclaration(
            name_token,
            .{ .for_loop_payload = .{ .identifier = name_token, .condition = input } },
            .other,
        );
    }

    if (for_node.label_token) |label_token| {
        try then_scope.pushDeclaration(
            for_node.label_token.?,
            .{ .label = .{ .identifier = label_token, .block = for_node.ast.then_expr } },
            .label,
        );
    }

    try then_scope.finalize();

    if (for_node.ast.else_expr.unwrap()) |else_expr| {
        if (for_node.label_token) |label_token| {
            const else_scope = try walkNodeEnsureScope(context, tree, else_expr, tree.firstToken(else_expr));
            try else_scope.pushDeclaration(
                for_node.label_token.?,
                .{ .label = .{ .identifier = label_token, .block = else_expr } },
                .label,
            );
            try else_scope.finalize();
        } else {
            try walkNode(context, tree, else_expr);
        }
    }
}

noinline fn walkSwitchNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    const full = tree.fullSwitch(node_idx).?;

    const switch_scope = if (full.label_token) |label_token| blk: {
        const scope = try context.startScope(
            .other,
            .{ .ast_node = node_idx },
            locToSmallLoc(offsets.nodeToLoc(tree, node_idx)),
        );
        try scope.pushDeclaration(
            label_token,
            .{ .label = .{ .identifier = label_token, .block = node_idx } },
            .label,
        );
        break :blk scope;
    } else null;

    try walkNode(context, tree, full.ast.condition);

    for (full.ast.cases, 0..) |case, case_index| {
        const switch_case: Ast.full.SwitchCase = tree.fullSwitchCase(case).?;

        for (switch_case.ast.values) |case_value| {
            try walkNode(context, tree, case_value);
        }

        if (switch_case.payload_token) |payload_token| {
            const name_token = payload_token + @intFromBool(tree.tokenTag(payload_token) == .asterisk);

            const expr_scope = try walkNodeEnsureScope(context, tree, switch_case.ast.target_expr, name_token);
            try expr_scope.pushDeclaration(
                name_token,
                .{ .switch_payload = .{ .node = node_idx, .case_index = @intCast(case_index) } },
                .other,
            );
            if (name_token + 2 < tree.tokens.len and
                tree.tokenTag(name_token + 1) == .comma and
                tree.tokenTag(name_token + 2) == .identifier)
            {
                try expr_scope.pushDeclaration(
                    name_token + 2,
                    .{ .switch_inline_tag_payload = .{ .node = node_idx, .case_index = @intCast(case_index) } },
                    .other,
                );
            }
            try expr_scope.finalize();
        } else {
            try walkNode(context, tree, switch_case.ast.target_expr);
        }
    }
    if (switch_scope) |scope| try scope.finalize();
}

noinline fn walkUnaryOpNode(context: *ScopeContext, tree: *const Ast, node_idx: Ast.Node.Index) error{OutOfMemory}!void {
    try walkNode(context, tree, tree.nodeData(node_idx).node);
}

noinline fn walkBinOpNode(context: *ScopeContext, tree: *const Ast, node_idx: Ast.Node.Index) error{OutOfMemory}!void {
    const lhs, const rhs = tree.nodeData(node_idx).node_and_node;
    try walkNode(context, tree, lhs);
    try walkNode(context, tree, rhs);
}

noinline fn walkOptNodeAndOptNode(context: *ScopeContext, tree: *const Ast, node_idx: Ast.Node.Index) error{OutOfMemory}!void {
    const opt_lhs, const opt_rhs = tree.nodeData(node_idx).opt_node_and_opt_node;
    if (opt_lhs.unwrap()) |lhs| try walkNode(context, tree, lhs);
    if (opt_rhs.unwrap()) |rhs| try walkNode(context, tree, rhs);
}

noinline fn walkNodeAndOptNode(context: *ScopeContext, tree: *const Ast, node_idx: Ast.Node.Index) error{OutOfMemory}!void {
    const lhs, const opt_rhs = tree.nodeData(node_idx).node_and_opt_node;
    try walkNode(context, tree, lhs);
    if (opt_rhs.unwrap()) |rhs| try walkNode(context, tree, rhs);
}

noinline fn walkOtherNode(
    context: *ScopeContext,
    tree: *const Ast,
    node_idx: Ast.Node.Index,
) error{OutOfMemory}!void {
    var it: ast.Iterator = .init(tree, node_idx);
    while (it.next(tree)) |child| try walkNode(context, tree, child);
}

// Lookup

pub fn getScopeTag(
    doc_scope: DocumentScope,
    scope: Scope.Index,
) Scope.Tag {
    return doc_scope.scopes.items(.data)[@intFromEnum(scope)].tag;
}

pub fn getScopeParent(
    doc_scope: DocumentScope,
    scope: Scope.Index,
) Scope.OptionalIndex {
    return doc_scope.scopes.items(.parent_scope)[@intFromEnum(scope)];
}

pub fn getScopeAstNode(
    doc_scope: DocumentScope,
    scope: Scope.Index,
) ?Ast.Node.Index {
    const slice = doc_scope.scopes.slice();

    const data = slice.items(.data)[@intFromEnum(scope)];

    return switch (data.tag) {
        .container, .function, .block => data.data.ast_node,
        .other => null,
    };
}

pub fn getScopeDeclaration(
    doc_scope: DocumentScope,
    lookup: DeclarationLookup,
) Declaration.OptionalIndex {
    return if (doc_scope.declaration_lookup_map.getIndex(lookup)) |idx|
        @enumFromInt(idx)
    else
        .none;
}

pub fn getScopeDeclarationsConst(
    doc_scope: DocumentScope,
    scope: Scope.Index,
) []const Declaration.Index {
    const slice = doc_scope.scopes.slice();

    if (slice.items(.data)[@intFromEnum(scope)].is_child_decls_small) {
        const small = &slice.items(.child_declarations)[@intFromEnum(scope)].small;

        for (0..Scope.ChildDeclarations.small_size) |idx| {
            if (small[idx] == .none) {
                return @ptrCast(small[0..idx]);
            }
        }

        return @ptrCast(small[0..Scope.ChildDeclarations.small_size]);
    } else {
        const other = slice.items(.child_declarations)[@intFromEnum(scope)].other;
        return @ptrCast(doc_scope.extra.items[other.start..other.end]);
    }
}

pub fn getScopeChildScopesConst(
    doc_scope: DocumentScope,
    scope: Scope.Index,
) []const Scope.Index {
    const slice = doc_scope.scopes.slice();

    if (slice.items(.data)[@intFromEnum(scope)].is_child_scopes_small) {
        const small = &slice.items(.child_scopes)[@intFromEnum(scope)].small;

        for (0..Scope.ChildScopes.small_size) |idx| {
            if (small[idx] == .none) {
                return @ptrCast(small[0..idx]);
            }
        }

        return @ptrCast(small[0..Scope.ChildScopes.small_size]);
    } else {
        const other = slice.items(.child_scopes)[@intFromEnum(scope)].other;
        return @ptrCast(doc_scope.extra.items[other.start..other.end]);
    }
}

test "an errdefer payload is declared in the deferred body only" {
    const gpa = std.testing.allocator;

    // A consumer Zig itself accepts: the capture shadows nothing (Zig forbids
    // that), `incoming` is a real parameter of `foo`, and `foo` really returns
    // an error, so there is something for the errdefer to defer for.  `handle`
    // takes a parameter named `err` as well, so a lookup of `err` that escaped
    // `foo` would find that parameter instead of finding nothing at all.
    const source =
        \\fn handle(err: anyerror) void {
        \\    _ = err;
        \\}
        \\
        \\fn use(value: anyerror) void {
        \\    _ = value;
        \\}
        \\
        \\fn foo(incoming: anyerror) !void {
        \\    errdefer |err| {
        \\        handle(err);
        \\        _ = err;
        \\    }
        \\    _ = incoming;
        \\    use(incoming);
        \\    return error.Boom;
        \\}
        \\
    ;

    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);

    var document_scope = try init(gpa, &tree);
    defer document_scope.deinit(gpa);

    // Name lookup the way `analysis.lookupSymbolGlobal` performs it: start at
    // the innermost scope covering a source index, then ask every enclosing
    // scope for an `.other` declaration of that name.
    const Lookup = struct {
        fn innermost(doc_scope: *const DocumentScope, source_index: usize) Scope.Index {
            var current: Scope.Index = .root;
            descend: while (true) {
                for (doc_scope.getScopeChildScopesConst(current)) |child| {
                    const loc = doc_scope.scopes.items(.loc)[@intFromEnum(child)];
                    const start: usize = loc.start;
                    const end: usize = loc.end;
                    if (source_index < start or end < source_index) continue;
                    current = child;
                    continue :descend;
                }
                return current;
            }
        }

        fn other(
            doc_scope: *const DocumentScope,
            source_index: usize,
            name: []const u8,
        ) ?Declaration.Index {
            var scope = innermost(doc_scope, source_index);
            while (true) {
                if (doc_scope.getScopeDeclaration(.{
                    .scope = scope,
                    .name = name,
                    .kind = .other,
                }).unwrap()) |decl_index| return decl_index;
                scope = doc_scope.getScopeParent(scope).unwrap() orelse return null;
            }
        }
    };

    // `foo` is the function holding the errdefer; it is looked up by name so
    // the parameter check below can name the function it belongs to.
    var proto_buffer: [1]Ast.Node.Index = undefined;
    var foo_fn: ?Ast.Node.Index = null;
    for (0..tree.nodes.items(.tag).len) |i| {
        const node: Ast.Node.Index = @enumFromInt(i);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const proto = tree.fullFnProto(&proto_buffer, node).?;
        const name = tree.tokenSlice(proto.name_token orelse continue);
        if (!std.mem.eql(u8, name, "foo")) continue;
        foo_fn = node;
        break;
    }
    const foo_node = foo_fn orelse return error.TestUnexpectedResult;

    var statement_buffer: [2]Ast.Node.Index = undefined;
    const foo_body = tree.nodeData(foo_node).node_and_node[1];
    const foo_statements = tree.blockStatements(&statement_buffer, foo_body).?;

    // The statement behind the errdefer is `_ = incoming;`, a real use of the
    // parameter that lies outside the deferred body.
    const errdefer_at = for (foo_statements, 0..) |stmt, i| {
        if (tree.nodeTag(stmt) != .@"errdefer") continue;
        break i;
    } else return error.TestUnexpectedResult;
    if (errdefer_at + 1 >= foo_statements.len) return error.TestUnexpectedResult;
    const errdefer_stmt = foo_statements[errdefer_at];
    const stmt_after_errdefer = foo_statements[errdefer_at + 1];

    const deferred_body = tree.nodeData(errdefer_stmt).opt_token_and_node[1];
    var body_statement_buffer: [2]Ast.Node.Index = undefined;
    const body_statements = tree.blockStatements(&body_statement_buffer, deferred_body).?;
    // `_ = err;`, the use of the capture that has to resolve.
    const capture_use = for (body_statements) |stmt| {
        if (!std.mem.eql(u8, tree.tokenSlice(tree.firstToken(stmt)), "_")) continue;
        break stmt;
    } else return error.TestUnexpectedResult;

    // Inside the deferred body `err` resolves, and the scope covering that use
    // is the deferred body itself and owns the payload directly, so no outer
    // binding can be reached through it.
    const inside_body = tree.tokenStart(tree.firstToken(capture_use));
    const payload_index = Lookup.other(&document_scope, inside_body, "err") orelse
        return error.TestUnexpectedResult;
    try std.testing.expect(document_scope.declarations.get(@intFromEnum(payload_index)) == .error_union_error);

    const owning_scope = Lookup.innermost(&document_scope, inside_body);
    try std.testing.expectEqual(deferred_body, getScopeAstNode(document_scope, owning_scope) orelse
        return error.TestUnexpectedResult);
    try std.testing.expectEqual(
        payload_index,
        getScopeDeclaration(document_scope, .{ .scope = owning_scope, .name = "err", .kind = .other }).unwrap() orelse
            return error.TestUnexpectedResult,
    );

    // Behind the errdefer `incoming` is still the parameter of `foo`...
    const after_body = tree.tokenStart(tree.firstToken(stmt_after_errdefer));
    const incoming_index = Lookup.other(&document_scope, after_body, "incoming") orelse
        return error.TestUnexpectedResult;
    const incoming = document_scope.declarations.get(@intFromEnum(incoming_index));
    try std.testing.expect(incoming == .function_parameter);
    try std.testing.expectEqual(foo_node, incoming.function_parameter.func);

    // ...and the payload is gone: nothing named `err` is in scope there, even
    // though `handle` has a parameter of that name.
    try std.testing.expect(Lookup.other(&document_scope, after_body, "err") == null);
}
