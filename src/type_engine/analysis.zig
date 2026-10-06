//! The ZLS analysis backend.
//!
//! The most frequently used functions are:
//! - `resolveTypeOfNode`
//! - `getPositionContext`
//! - `lookupSymbolGlobal`
//! - `lookupSymbolContainer`
//!

const builtin = @import("builtin");
const std = @import("std");
const DocumentStore = @import("document_store.zig");
const Ast = std.zig.Ast;
const offsets = @import("offsets.zig");
const Uri = @import("uri.zig");
const log = std.log.scoped(.analysis);
const ast = @import("ast.zig");
const tracy = @import("tracy_stub.zig");
const InternPool = @import("intern_pool.zig");
const ErrorMsg = @import("error_msg.zig").ErrorMsg;

pub const DocumentScope = @import("document_scope.zig");
pub const Declaration = DocumentScope.Declaration;
pub const Scope = DocumentScope.Scope;

const version_data = @import("version_data.zig");

const Analyser = @This();

gpa: std.mem.Allocator,
arena: std.mem.Allocator,
store: *DocumentStore,
ip: *InternPool,
/// Answers that are already settled, keyed by the whole question and not
/// by the formal alone.  Only a REAL answer is stored: a null here would
/// be indistinguishable from "not started yet", and "still being worked
/// out" is `resolving_callsites` below instead.
resolved_callsites: std.HashMapUnmanaged(CallsiteKey, Type, CallsiteKey.Context, std.hash_map.default_max_load_percentage) = .empty,
/// The keys whose call sites are being aggregated right now.  The walk
/// nests strictly, so this is a stack and push/pop is the protocol.
resolving_callsites: std.ArrayList(CallsiteKey) = .empty,
resolved_nodes: std.HashMapUnmanaged(NodeWithUri, ?Binding, NodeWithUri.Context, std.hash_map.default_max_load_percentage) = .empty,
collect_callsite_references: bool,
/// handle of the doc where the request originated
root_handle: ?DocumentStore.Handle,
max_conditional_combos: usize = 200,
/// The instantiation whose ACTUAL comptime argument values are bound
/// while a declaration resolves, or null outside one.
comptime_values: ?*const ComptimeValues = null,
/// One scope per container instantiation that binds values, so repeated
/// resolutions of the same instantiation share one pointer — and with
/// it, one `NodeWithUri` cache key.
comptime_value_scopes: ComptimeValueScopeMap = .empty,

/// One `anytype` formal of one declaration, read under one ACTUAL
/// container.
///
/// `Declaration.Param` on its own is not an identity for the answer this
/// cache holds.  It is `{ param_index, func }` — no document, no module,
/// no container — while the answer is the union of the types every call
/// site supplies, and WHICH call sites count is itself decided by the
/// container the formal is being read under.  Two instantiations of one
/// generic declaration reach the same `Param` through different frames,
/// so a key that stops at `Param` would serve one instantiation's union
/// to the other.
///
/// The handle says which declaration this formal belongs to (the same
/// physical file read in two modules is two declarations); the container
/// says which instantiation is asking.
const CallsiteKey = struct {
    param: Declaration.Param,
    handle: DocumentStore.Handle,
    container_type: ?Type,

    const Context = struct {
        pub fn hash(_: Context, key: CallsiteKey) u64 {
            var hasher: std.hash.Wyhash = .init(0);
            hasher.update(key.handle.document.uri.raw);
            std.hash.autoHash(&hasher, key.handle.module);
            std.hash.autoHash(&hasher, key.param);
            if (key.container_type) |ty| ty.hashWithHasher(&hasher);
            return hasher.final();
        }

        pub fn eql(_: Context, a: CallsiteKey, b: CallsiteKey) bool {
            if (a.handle.module != b.handle.module) return false;
            if (!a.handle.document.uri.eql(b.handle.document.uri)) return false;
            if (!std.meta.eql(a.param, b.param)) return false;
            if ((a.container_type == null) != (b.container_type == null)) return false;
            if (a.container_type) |ty| {
                if (!ty.eql(b.container_type.?)) return false;
            }
            return true;
        }
    };
};

const NodeSet = std.HashMapUnmanaged(NodeWithUri, void, NodeWithUri.Context, std.hash_map.default_max_load_percentage);

pub const Error = std.mem.Allocator.Error || std.Io.Cancelable || error{SourceExcluded};

pub fn init(
    gpa: std.mem.Allocator,
    arena: std.mem.Allocator,
    store: *DocumentStore,
    ip: *InternPool,
    root_handle: ?DocumentStore.Handle,
) Analyser {
    return .{
        .gpa = gpa,
        .arena = arena,
        .store = store,
        .ip = ip,
        .collect_callsite_references = true,
        .root_handle = root_handle,
    };
}

pub fn deinit(self: *Analyser) void {
    self.resolved_callsites.deinit(self.gpa);
    self.resolving_callsites.deinit(self.gpa);
    self.resolved_nodes.deinit(self.gpa);
    self.comptime_value_scopes.deinit(self.gpa);
}

fn allocType(analyser: *Analyser, ty: Type) error{OutOfMemory}!*Type {
    const ptr = try analyser.arena.create(Type);
    ptr.* = ty;
    return ptr;
}

/// The ACTUAL comptime values bound to the parameters of ONE generic
/// instantiation, e.g. `digest_bits -> 224` for `Sha2x32(iv224, 224)`.
///
/// A separate thing from the type bindings in
/// `Type.Data.Container.bound_params`: a bound value is not a type.
/// `digest_bits` is declared `comptime_int`, and the engine could only
/// ever spell that as "a `comptime_int` with no value", which is why
/// `ip.toInt` answered null and every extent derived from it stayed
/// unknown.
///
/// `Sha2x32(iv224, 224)` and `Sha2x32(iv256, 256)` share one AST, one
/// module and one container declaration and differ only here, so a node
/// cache keyed on the AST alone cannot represent both — which is why the
/// scope is part of the `NodeWithUri` key.
const ComptimeValues = struct {
    map: ComptimeValueMap,

    pub fn get(self: ComptimeValues, token: TokenWithHandle) ?InternPool.Index {
        return self.map.get(token);
    }
};

const ComptimeValueMap = std.HashMapUnmanaged(
    TokenWithHandle,
    InternPool.Index,
    ComptimeValueMapContext,
    std.hash_map.default_max_load_percentage,
);

const ComptimeValueMapContext = struct {
    pub fn hash(_: ComptimeValueMapContext, token: TokenWithHandle) u64 {
        var hasher: std.hash.Wyhash = .init(0);
        token.hashWithHasher(&hasher);
        return hasher.final();
    }

    pub fn eql(_: ComptimeValueMapContext, a: TokenWithHandle, b: TokenWithHandle) bool {
        return a.eql(b);
    }
};

const ComptimeValueScopeMap = std.HashMapUnmanaged(
    Type,
    *ComptimeValues,
    ComptimeValueScopeMapContext,
    std.hash_map.default_max_load_percentage,
);

const ComptimeValueScopeMapContext = struct {
    pub fn hash(_: ComptimeValueScopeMapContext, ty: Type) u64 {
        return ty.hash64();
    }

    pub fn eql(_: ComptimeValueScopeMapContext, a: Type, b: Type) bool {
        return a.eql(b);
    }
};

/// The value scope `container`'s own members resolve under, or null when
/// it binds none — the common case, which then costs nothing.
///
/// Scopes do not nest: resolving a declaration of one instantiation
/// while another is open uses the inner one alone.  That can only
/// withhold a value, never invent one, so an unbound parameter stays
/// unknown exactly as it was before.
fn comptimeValuesOfContainer(analyser: *Analyser, container: ?Type) Error!?*ComptimeValues {
    const container_ty = container orelse return null;
    const info = switch (container_ty.data) {
        .container => |info| info,
        else => return null,
    };
    if (info.bound_params.count() == 0) return null;
    if (analyser.comptime_value_scopes.get(container_ty)) |scope| return scope;

    const scope = try analyser.arena.create(ComptimeValues);
    scope.* = .{ .map = .empty };
    for (info.bound_params.keys(), info.bound_params.values()) |token_handle, ty| {
        // Only a bound VALUE belongs here.  A type binding is already
        // substituted by `resolveGenericType`, and that substitution
        // asserts its result is a type.
        if (ty.is_type_val) continue;
        const value_index = ty.ipIndex() orelse continue;
        try scope.map.put(analyser.arena, token_handle, value_index);
    }
    if (scope.map.count() == 0) return null;

    const gop = try analyser.comptime_value_scopes.getOrPut(analyser.gpa, container_ty);
    if (gop.found_existing) return gop.value_ptr.*;
    gop.value_ptr.* = scope;
    return scope;
}

pub fn getDocCommentsBeforeToken(allocator: std.mem.Allocator, tree: *const Ast, base: Ast.TokenIndex) error{OutOfMemory}!?[]const u8 {
    const doc_comment_index = getDocCommentTokenIndex(tree, base) orelse return null;
    return try collectDocComments(allocator, tree, doc_comment_index, false);
}

/// Gets a declaration's doc comments. Caller owns returned memory.
pub fn getDocComments(allocator: std.mem.Allocator, tree: *const Ast, node: Ast.Node.Index) error{OutOfMemory}!?[]const u8 {
    const base = tree.nodeMainToken(node);
    const base_kind = tree.nodeTag(node);

    switch (base_kind) {
        .root => return try collectDocComments(allocator, tree, 0, true),
        .fn_proto,
        .fn_proto_one,
        .fn_proto_simple,
        .fn_proto_multi,
        .fn_decl,
        .local_var_decl,
        .global_var_decl,
        .aligned_var_decl,
        .simple_var_decl,
        .container_field_init,
        .container_field_align,
        .container_field,
        => return try getDocCommentsBeforeToken(allocator, tree, base),
        else => {},
    }
    return null;
}

/// Get the first doc comment of a declaration.
pub fn getDocCommentTokenIndex(tree: *const Ast, base_token: Ast.TokenIndex) ?Ast.TokenIndex {
    var idx = base_token;
    if (idx == 0) return null;
    idx -|= 1;
    if (tree.tokenTag(idx) == .keyword_threadlocal and idx > 0) idx -|= 1;
    if (tree.tokenTag(idx) == .string_literal and idx > 1 and tree.tokenTag(idx -| 1) == .keyword_extern) idx -|= 1;
    if (tree.tokenTag(idx) == .keyword_extern and idx > 0) idx -|= 1;
    if (tree.tokenTag(idx) == .keyword_export and idx > 0) idx -|= 1;
    if (tree.tokenTag(idx) == .keyword_inline and idx > 0) idx -|= 1;
    if (tree.tokenTag(idx) == .identifier and idx > 0) idx -|= 1;
    if (tree.tokenTag(idx) == .keyword_pub and idx > 0) idx -|= 1;

    // Find first doc comment token
    if (!(tree.tokenTag(idx) == .doc_comment))
        return null;
    return while (tree.tokenTag(idx) == .doc_comment) {
        if (idx == 0) break 0;
        idx -|= 1;
    } else idx + 1;
}

pub fn collectDocComments(
    allocator: std.mem.Allocator,
    tree: *const Ast,
    doc_comments: Ast.TokenIndex,
    container_doc: bool,
) error{OutOfMemory}!?[]const u8 {
    var lines: std.ArrayList([]const u8) = .empty;
    defer lines.deinit(allocator);

    var lines_start_with_space = true;

    var curr_line_tok = doc_comments;
    while (true) : (curr_line_tok += 1) {
        switch (tree.tokenTag(curr_line_tok)) {
            .container_doc_comment => if (!container_doc) break,
            .doc_comment => if (container_doc) break,
            else => break,
        }
        const line = tree.tokenSlice(curr_line_tok)[3..];
        if (!std.mem.startsWith(u8, line, " ")) lines_start_with_space = false;
        try lines.append(allocator, line);
    }
    if (lines.items.len == 0) return null;

    // If all of the lines that aren't empty start with a space, remove the first space
    if (lines_start_with_space) {
        for (lines.items, 0..) |line, i| {
            if (line.len > 1 and line[0] == ' ') {
                lines.items[i] = line[1..];
            }
        }
    }

    return try std.mem.join(allocator, "\n", lines.items);
}

/// Gets a function's keyword, name, arguments and return value.
pub fn getFunctionSignature(tree: *const Ast, func: Ast.full.FnProto) []const u8 {
    const first_token = func.ast.fn_token;
    const last_token = if (func.ast.return_type.unwrap()) |return_type| ast.lastToken(tree, return_type) else first_token;
    return offsets.tokensToSlice(tree, first_token, last_token);
}

pub const FormatParameterOptions = struct {
    referenced: ?*ReferencedType.Set = null,
    info: Type.Data.Parameter,

    include_modifier: bool,
    include_name: bool,
    include_type: bool,
};

pub fn stringifyParameter(analyser: *Analyser, options: FormatParameterOptions) error{OutOfMemory}![]u8 {
    var aw: std.Io.Writer.Allocating = .init(analyser.arena);
    defer aw.deinit();
    analyser.rawStringifyParameter(&aw.writer, options) catch |err| switch (err) {
        error.OutOfMemory, error.WriteFailed => return error.OutOfMemory,
    };
    return try aw.toOwnedSlice();
}

fn rawStringifyParameter(
    analyser: *Analyser,
    writer: *std.Io.Writer,
    options: FormatParameterOptions,
) error{ OutOfMemory, WriteFailed }!void {
    const referenced = options.referenced;
    const info = options.info;

    // Note that parameter doc comments are being skipped

    if (options.include_modifier) {
        if (info.modifier) |modifier| {
            switch (modifier) {
                .comptime_param => try writer.writeAll("comptime "),
                .noalias_param => try writer.writeAll("noalias "),
            }
        }
    }

    if (options.include_name) {
        if (info.name) |name| {
            try writer.writeAll(name);
        }
    }

    if (options.include_type) {
        const has_parameter_name = options.include_name and info.name != null;
        if (has_parameter_name) try writer.writeAll(": ");

        try info.type.rawStringify(writer, analyser, .{
            .referenced = referenced,
            .truncate_container_decls = true,
        });
    }
}

pub const FormatFunctionOptions = struct {
    referenced: ?*ReferencedType.Set = null,
    info: Type.Data.Function,

    include_fn_keyword: bool,
    /// only included if available
    include_name: bool,
    override_name: ?[]const u8 = null,
    skip_first_param: bool = false,
    parameters: union(enum) {
        collapse,
        show: struct {
            include_modifiers: bool,
            include_names: bool,
            include_types: bool,
        },
    },
    include_return_type: bool,
    snippet_placeholders: bool,
};

pub fn stringifyFunction(analyser: *Analyser, options: FormatFunctionOptions) error{OutOfMemory}![]u8 {
    var aw: std.Io.Writer.Allocating = .init(analyser.arena);
    defer aw.deinit();
    analyser.rawStringifyFunction(&aw.writer, options) catch |err| switch (err) {
        error.OutOfMemory, error.WriteFailed => return error.OutOfMemory,
    };
    return try aw.toOwnedSlice();
}

fn rawStringifyFunction(
    analyser: *Analyser,
    writer: *std.Io.Writer,
    options: FormatFunctionOptions,
) error{ OutOfMemory, WriteFailed }!void {
    const referenced = options.referenced;
    const info = options.info;
    var parameters = info.parameters;

    var snippet_escaping_writer: SnippetEscapingWriter = .init(writer);
    const escaping_writer = if (options.snippet_placeholders) &snippet_escaping_writer.interface else writer;

    if (options.include_fn_keyword) {
        try writer.writeAll("fn ");
    }

    if (options.include_name) no_name: {
        const name = options.override_name orelse info.name orelse break :no_name;
        try escaping_writer.writeAll(name);
    }

    try writer.writeByte('(');

    if (options.skip_first_param) {
        if (parameters.len >= 1) {
            parameters = parameters[1..];
        }
    }

    switch (options.parameters) {
        .collapse => {
            const has_arguments = parameters.len != 0;
            if (has_arguments) {
                if (options.snippet_placeholders) {
                    try writer.writeAll("${1:...}");
                } else {
                    try writer.writeAll("...");
                }
            }
        },
        .show => |parameter_options| {
            for (parameters, 0..) |param_info, index| {
                if (index != 0) try writer.writeAll(", ");
                if (options.snippet_placeholders) {
                    try writer.print("${{{d}:", .{index + 1});
                }

                try analyser.rawStringifyParameter(escaping_writer, .{
                    .referenced = referenced,
                    .info = param_info,
                    .include_modifier = parameter_options.include_modifiers,
                    .include_name = parameter_options.include_names,
                    .include_type = parameter_options.include_types,
                });
                if (options.snippet_placeholders) {
                    try writer.writeByte('}');
                }
            }
        },
    }

    if (info.has_varargs) {
        if (parameters.len != 0) {
            try writer.writeAll(", ");
        }
        try writer.writeAll("...");
    }

    try writer.writeByte(')');

    // ignoring align_expr
    // ignoring addrspace_expr
    // ignoring section_expr
    // ignoring callconv_expr

    if (options.include_return_type) {
        try writer.writeByte(' ');

        const return_type = try options.info.return_value.typeOf(analyser);
        try return_type.rawStringify(escaping_writer, analyser, .{
            .referenced = referenced,
            .truncate_container_decls = true,
        });
    }
}

const SnippetEscapingWriter = struct {
    out: *std.Io.Writer,
    interface: std.Io.Writer,

    pub fn init(writer: *std.Io.Writer) SnippetEscapingWriter {
        return .{
            .out = writer,
            .interface = .{
                .vtable = &.{
                    .drain = &drain,
                    .flush = std.Io.Writer.noopFlush,
                    .rebase = std.Io.Writer.failingRebase,
                },
                .buffer = &.{},
            },
        };
    }

    fn drain(w: *std.Io.Writer, data: []const []const u8, splat: usize) std.Io.Writer.Error!usize {
        const self: *SnippetEscapingWriter = @fieldParentPtr("interface", w);
        const out = self.out;
        std.debug.assert(w.buffer.len == 0);
        for (data, 0..) |vec, i| {
            const segment_index = std.mem.findAny(u8, vec, "$}\\") orelse continue;
            if (i != 0) {
                return try out.writeSplat(data[0..i], splat);
            }
            const segment = vec[0..segment_index];
            const unescaped_char = vec[segment_index];
            const bytes_written = try out.write(segment);
            if (bytes_written < segment.len) return bytes_written;
            try out.writeAll(&.{ '\\', unescaped_char });
            return bytes_written + 1;
        } else {
            return try out.writeSplat(data, splat);
        }
    }

    fn writeAll(raw_text: []const u8, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        var written: usize = 0;
        for (raw_text, 0..) |c, i| {
            switch (c) {
                '$', '}', '\\' => {
                    try writer.writeAll(raw_text[written..i]);
                    try writer.writeAll(&.{ '\\', c });
                    written = i + 1;
                },
                else => continue,
            }
        }
        try writer.writeAll(raw_text[written..]);
    }
};

pub fn fmtEscapedSnippet(raw_text: []const u8) std.fmt.Alt([]const u8, SnippetEscapingWriter.writeAll) {
    return .{ .data = raw_text };
}

pub fn renderBuiltinFunctionSignature(
    arena: std.mem.Allocator,
    name: []const u8,
    builtin_data: version_data.Builtin,
    multi_line: bool,
) error{OutOfMemory}![]u8 {
    var signature: std.ArrayList(u8) = .empty;
    try signature.appendSlice(arena, name);
    try signature.append(arena, '(');
    if (multi_line) try signature.append(arena, '\n');
    for (builtin_data.parameters, 0..) |parameter, i| {
        if (multi_line) {
            try signature.appendSlice(arena, "  ");
        } else if (i != 0) {
            try signature.appendSlice(arena, ", ");
        }
        try signature.appendSlice(arena, parameter.signature);
        if (multi_line) {
            try signature.appendSlice(arena, ",\n");
        }
    }
    try signature.appendSlice(arena, ") ");
    try signature.appendSlice(arena, builtin_data.return_type);
    return signature.items; // zbc-disable-line: return-arraylist-items — intentional arena-backed borrow; caller's arena owns the allocation
}

/// Is this call an instance call — one whose first argument is the
/// receiver the callee is declared in?
///
/// `options` is the CALLER's frame, because the receiver is written in the
/// caller's body: resolving `receiver.method()` under a container the
/// caller never opened would answer about a different receiver than the
/// one the source names.  Arity is the caller's business and stays here:
/// this function decides only whether the receiver binds.
pub fn isInstanceCall(
    analyser: *Analyser,
    options: ResolveOptions,
    call: Ast.full.Call,
    func_ty: Type,
) Error!bool {
    const call_handle = options.node_handle.handle;
    std.debug.assert(!func_ty.is_type_val);
    if (call_handle.document.tree.nodeTag(call.ast.fn_expr) != .field_access) return false;

    const container_node, _ = call_handle.document.tree.nodeData(call.ast.fn_expr).node_and_token;

    const container_ty = if (try analyser.resolveTypeOfNodeInternal(options.at(container_node))) |container_instance|
        try container_instance.typeOf(analyser)
    else blk: {
        // The receiver does not resolve, so the callee's OWN container is
        // what this call is being read as.  `firstParamIs` below needs a
        // type value, and a function reached through a bound receiver
        // carries the container as an INSTANCE — so normalize here, in the
        // one authority that owns the decision.
        //
        // An ALREADY type-valued container is preserved untouched:
        // `Type.typeOf` answers `type_type` for one, which is a different
        // question than the container we already hold.
        const own = func_ty.data.function.container_type.*;
        break :blk if (own.is_type_val) own else try own.typeOf(analyser);
    };

    std.debug.assert(container_ty.is_type_val);

    return analyser.firstParamIs(func_ty, container_ty);
}

pub fn hasSelfParam(analyser: *Analyser, func_ty: Type) error{OutOfMemory}!bool {
    std.debug.assert(func_ty.isFunc());
    const container = func_ty.data.function.container_type.*;
    if (container.is_type_val) return false;
    const in_container = try container.typeOf(analyser);
    if (in_container.isNamespace()) return false;
    return analyser.firstParamIs(func_ty, in_container);
}

pub fn firstParamIs(
    analyser: *Analyser,
    func_type: Type,
    expected_type: Type,
) bool {
    _ = analyser;
    std.debug.assert(expected_type.is_type_val);
    std.debug.assert(func_type.isFunc());
    const func_info = func_type.data.function;
    if (func_info.parameters.len == 0) return false;
    const resolved_type = func_info.parameters[0].type;
    if (!resolved_type.is_type_val) return false;
    if (resolved_type.data == .anytype_parameter) return true;

    const deref_type = switch (resolved_type.data) {
        .pointer => |info| switch (info.size) {
            .one, .c => info.elem_ty.*,
            .many, .slice => return false,
        },
        else => resolved_type,
    };

    const deref_expected_type = switch (expected_type.data) {
        .pointer => |info| switch (info.size) {
            .one, .c => info.elem_ty.*,
            .many, .slice => return false,
        },
        else => expected_type,
    };

    return switch (deref_type.data) {
        .either => |entries| {
            for (entries) |entry| {
                if (entry.type_data.eql(deref_expected_type.data)) {
                    return true;
                }
            }
            return false;
        },
        else => deref_type.eql(deref_expected_type),
    };
}

pub fn getVariableSignature(
    arena: std.mem.Allocator,
    tree: *const Ast,
    var_decl: Ast.full.VarDecl,
    include_name: bool,
) error{OutOfMemory}![]const u8 {
    const start_token = if (include_name)
        var_decl.ast.mut_token
    else if (var_decl.ast.type_node.unwrap()) |type_node|
        tree.firstToken(type_node)
    else if (var_decl.ast.init_node.unwrap()) |init_node|
        tree.firstToken(init_node)
    else
        return "";

    const init_node = var_decl.ast.init_node.unwrap() orelse {
        const type_node = var_decl.ast.type_node.unwrap() orelse return "";
        return offsets.tokensToSlice(tree, start_token, ast.lastToken(tree, type_node));
    };

    const end_token = switch (tree.nodeTag(init_node)) {
        .container_decl,
        .container_decl_trailing,
        .container_decl_arg,
        .container_decl_arg_trailing,
        .container_decl_two,
        .container_decl_two_trailing,
        .tagged_union,
        .tagged_union_trailing,
        .tagged_union_enum_tag,
        .tagged_union_enum_tag_trailing,
        .tagged_union_two,
        .tagged_union_two_trailing,
        => end_token: {
            var buf: [2]Ast.Node.Index = undefined;
            const container_decl = tree.fullContainerDecl(&buf, init_node).?;

            var token = container_decl.ast.main_token;
            var offset: Ast.TokenIndex = 0;

            // Tagged union: union(enum)
            if (container_decl.ast.enum_token) |enum_token| {
                token = enum_token;
                offset += 1;
            }

            // Backing integer: struct(u32), union(enum(u32))
            // Tagged union: union(ComplexTypeTag)
            if (container_decl.ast.arg.unwrap()) |arg| {
                token = ast.lastToken(tree, arg);
                offset += 1;
            }

            if (container_decl.ast.members.len == 0) break :end_token token + offset;

            // e.g. 'pub const Mode = enum { zig, zon };'
            if (tree.tokensOnSameLine(tree.firstToken(init_node), ast.lastToken(tree, init_node))) {
                break :end_token ast.lastToken(tree, init_node);
            }

            var members_source: std.ArrayList(u8) = .empty;

            for (container_decl.ast.members) |member| {
                const member_line_start = offsets.lineLocUntilIndex(tree.source, tree.tokenStart(tree.firstToken(member))).start;

                const member_source_indented = switch (tree.nodeTag(member)) {
                    .container_field_init,
                    .container_field_align,
                    .container_field,
                    => tree.source[member_line_start..offsets.tokenToLoc(tree, ast.lastToken(tree, member)).end],
                    else => continue,
                };
                try members_source.append(arena, '\n');
                try members_source.appendSlice(arena, try trimCommonIndentation(arena, member_source_indented, 4));
                try members_source.append(arena, ',');
            }

            if (members_source.items.len == 0) break :end_token token + offset;

            return try std.mem.concat(arena, u8, &.{
                offsets.tokensToSlice(tree, start_token, token + offset),
                " {",
                members_source.items,
                "\n}",
            });
        },
        else => ast.lastToken(tree, init_node),
    };

    return offsets.tokensToSlice(tree, start_token, end_token);
}

fn trimCommonIndentation(allocator: std.mem.Allocator, str: []const u8, preserved_indentation_amount: usize) error{OutOfMemory}![]u8 {
    var line_it = std.mem.splitScalar(u8, str, '\n');

    var non_empty_lines: usize = 0;
    var min_indentation: ?usize = null;
    while (line_it.next()) |line| {
        if (line.len == 0) continue;
        const indentation = for (line, 0..) |c, count| {
            if (!std.ascii.isWhitespace(c)) break count;
        } else line.len;
        min_indentation = if (min_indentation) |old| @min(old, indentation) else indentation;
        non_empty_lines += 1;
    }

    var common_indent = min_indentation orelse return try allocator.dupe(u8, str);
    common_indent -|= preserved_indentation_amount;
    if (common_indent == 0) return try allocator.dupe(u8, str);

    const capacity = str.len - non_empty_lines * common_indent;
    var output: std.ArrayList(u8) = try .initCapacity(allocator, capacity);
    std.debug.assert(capacity == output.capacity);
    errdefer @compileError("error would leak here");

    line_it = std.mem.splitScalar(u8, str, '\n');
    var is_first_line = true;
    while (line_it.next()) |line| {
        if (!is_first_line) output.appendAssumeCapacity('\n');
        if (line.len != 0) {
            output.appendSliceAssumeCapacity(line[common_indent..]);
        }
        is_first_line = false;
    }

    std.debug.assert(output.items.len == output.capacity);
    return output.items;
}

test trimCommonIndentation {
    const cases = [_]struct { []const u8, []const u8, usize }{
        .{ "", "", 0 },
        .{ "\n", "\n", 0 },
        .{ "foo", "foo", 0 },
        .{ "foo", "  foo", 0 },
        .{ "foo  ", "    foo  ", 0 },
        .{ "foo\nbar", "    foo\n    bar", 0 },
        .{ "foo\nbar\n", "  foo\n  bar\n", 0 },
        .{ "  foo\nbar", "    foo\n  bar", 0 },
        .{ "foo\n  bar", "    foo\n      bar", 0 },
        .{ "  foo\n\nbar", "    foo\n\n  bar", 0 },

        .{ "  foo\n  bar", "    foo\n    bar", 2 },
        .{ "    foo\n    bar", "    foo\n    bar", 4 },
        .{ "    foo\n    bar", "    foo\n    bar", 8 },
    };

    for (cases) |case| {
        const actual = try trimCommonIndentation(std.testing.allocator, case[1], case[2]);
        defer std.testing.allocator.free(actual);
        try std.testing.expectEqualStrings(case[0], actual);
    }
}

/// One whole analyser over one in-memory document.
///
/// The store's `config` and the store's `modules` registry point back at
/// this allocation, so the fixture is heap allocated and never moved
/// after `create` — moving it would leave both dangling.
const AnalyserFixture = struct {
    arena: std.heap.ArenaAllocator,
    ip: InternPool,
    environ_map: std.process.Environ.Map,
    diagnostics: @import("diagnostics_collection.zig"),
    modules: DocumentStore.ModuleRegistry,
    store: DocumentStore,
    handle: DocumentStore.Handle,
    analyser: Analyser,

    fn create(gpa: std.mem.Allocator, file_name: []const u8, source: [:0]const u8) !*AnalyserFixture {
        const self = try gpa.create(AnalyserFixture);
        errdefer gpa.destroy(self);

        self.* = .{
            .arena = .init(gpa),
            .ip = undefined,
            .environ_map = .init(gpa),
            .diagnostics = .{ .io = std.testing.io, .allocator = gpa },
            .modules = .init(gpa),
            .store = undefined,
            .handle = undefined,
            .analyser = undefined,
        };
        errdefer self.arena.deinit();
        errdefer self.modules.deinit();
        errdefer self.environ_map.deinit();

        self.ip = try InternPool.init(std.testing.io, gpa);
        errdefer self.ip.deinit(gpa);

        // The SDK-supported way to spell "where am I": `realPathFile` into
        // a caller-sized buffer.  The fixture never reads the filesystem
        // through this path — the document is opened from the text it was
        // handed — it only needs a canonical, absolute name for the URI.
        var cwd_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const cwd_len = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &cwd_buffer);
        const path = try std.fs.path.join(gpa, &.{ cwd_buffer[0..cwd_len], file_name });
        defer gpa.free(path);
        const uri = try Uri.fromPath(self.arena.allocator(), path);

        self.store = .{
            .io = std.testing.io,
            .allocator = gpa,
            .modules = &self.modules,
            .config = .{
                .environ_map = &self.environ_map,
                .zig_exe_path = null,
                .zig_lib_dir = null,
                .build_runner_path = null,
                .builtin_path = null,
                .global_cache_dir = null,
                .wasi_preopens = {},
            },
            .diagnostics_collection = &self.diagnostics,
        };
        errdefer self.store.deinit();

        try self.store.openLspSyncedDocument(uri, source);
        self.handle = self.store.getHandle(uri, .unscoped) orelse return error.HandleMissing;
        try std.testing.expectEqual(@as(usize, 0), self.handle.document.tree.errors.len);

        self.analyser = .init(gpa, self.arena.allocator(), &self.store, &self.ip, self.handle);
        return self;
    }

    fn destroy(self: *AnalyserFixture, gpa: std.mem.Allocator) void {
        self.analyser.deinit();
        self.store.deinit();
        self.modules.deinit();
        self.environ_map.deinit();
        self.ip.deinit(gpa);
        self.arena.deinit();
        gpa.destroy(self);
    }

    fn tree(self: *AnalyserFixture) *const Ast {
        return &self.handle.document.tree;
    }
};

/// The call `callee(first_arg, …)` written anywhere in `tree`.  An empty
/// `first_arg` matches any first argument, including a call with none.
fn findCall(tree: *const Ast, callee: []const u8, first_arg: []const u8) error{ CallNotFound }!Ast.Node.Index {
    return findCallFrom(tree, callee, first_arg, 0);
}

/// The same, starting at node `from`.  One generic function called from two
/// containers in one file has two call sites, and the second look has to
/// start past the first.
fn findCallFrom(tree: *const Ast, callee: []const u8, first_arg: []const u8, from: usize) error{ CallNotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (raw < from) continue;
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), callee)) continue;
        if (first_arg.len == 0) return node;
        if (call.ast.params.len == 0) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.firstToken(call.ast.params[0])), first_arg)) continue;
        return node;
    }
    return error.CallNotFound;
}

/// The first argument the call at `call_node` was given.
fn callArgument(tree: *const Ast, call_node: Ast.Node.Index) error{ NoCallArgument }!Ast.Node.Index {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, call_node) orelse return error.NoCallArgument;
    return call.ast.params[0];
}

/// The function `call_node` reaches, instantiated by that call site.
///
/// `from` is the function type to instantiate.  Passing null reads the
/// callee out of the document; passing an ALREADY instantiated type
/// re-instantiates it, which is what a generic function reached a second
/// time from inside a bound frame does.
fn instantiateCallAt(
    analyser: *Analyser,
    handle: DocumentStore.Handle,
    tree: *const Ast,
    call_node: Ast.Node.Index,
    from: ?Type,
) !Type {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, call_node).?;
    const base = if (from) |already| already else
        (try analyser.resolveTypeOfNode(.of(call.ast.fn_expr, handle))).?;
    const proto = (try analyser.resolveFuncProtoOfCallable(base)) orelse
        return error.NotCallable;
    return analyser.resolveFunctionTypeFromCall(.of(call.ast.fn_expr, handle), call, proto);
}

/// The same call instantiated while a frame is OPEN — the arguments are
/// read in `container`, which is the frame the call was written in.
///
/// `instantiateCallAt` reads the arguments with no frame, which is the
/// right question for a call that starts an instantiation and the wrong
/// one for a call INSIDE an already-instantiated function: `middle(field)`
/// written in `take`'s body can only forward `take`'s binding if the read
/// happens under `take`'s frame.  Nothing here invents a value — the
/// arguments are resolved by exactly the production path, under the frame
/// they are written in.
fn instantiateCallAtInFrame(
    analyser: *Analyser,
    handle: DocumentStore.Handle,
    tree: *const Ast,
    call_node: Ast.Node.Index,
    from: ?Type,
    container: ?Type,
) !Type {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, call_node).?;
    const base = if (from) |already| already else
        (try analyser.resolveTypeOfNode(.of(call.ast.fn_expr, handle))).?;
    const proto = (try analyser.resolveFuncProtoOfCallable(base)) orelse
        return error.NotCallable;
    return analyser.resolveFunctionTypeFromCall(.{
        .node_handle = .of(call.ast.fn_expr, handle),
        .container_type = container,
    }, call, proto);
}

test "re-binding a formal the container already binds replaces its value" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-rebind-test.zig", generic_actual_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    // `Wrap(u8)` first: this publishes `T -> u8` on the function's own
    // container.
    const bound_u8 = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "make", "u8"), null);
    const u8_field = (try lookupSymbolContainer(bound_u8.data.function.return_value.*, "one", .field)) orelse
        return error.FieldNotFound;
    const one_u8 = (try u8_field.resolveType(analyser)).?;

    // The SAME generic function, now reached again with `u64` — on top of
    // the type it already published.  The second call REPLACES `T`, so the
    // number of bound formals is identical either way and only the values
    // differ.
    const rebound = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "make", "u64"), bound_u8);
    try std.testing.expect(!rebound.data.function.container_type.*.eql(
        bound_u8.data.function.container_type.*,
    ));

    const u64_field = (try lookupSymbolContainer(rebound.data.function.return_value.*, "one", .field)) orelse
        return error.FieldNotFound;
    const one_u64 = (try u64_field.resolveType(analyser)).?;

    // The re-bound container answers with the NEW argument, not the one
    // it was published with.
    try std.testing.expect(one_u64.data == .ip_index);
    try std.testing.expect(!one_u64.eql(one_u8));
}

/// The `.name` enum-literal node written anywhere in `tree`.
fn findEnumLiteral(tree: *const Ast, name: []const u8) error{ EnumLiteralNotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .enum_literal) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) continue;
        return node;
    }
    return error.EnumLiteralNotFound;
}

/// A default field value that is an enum literal, in a container whose
/// field type IS the generic argument — so the ONE `.off` node means a
/// different tag type under each instantiation, and reading it means
/// recovering the expected type from that instantiation's own field.
const generic_enum_default_source: [:0]const u8 =
    \\const Flag8 = enum(u8) { off, on };
    \\const Flag32 = enum(u32) { off, on };
    \\
    \\const Wrap = struct {
    \\    fn make(comptime Flag: type) type {
    \\        return struct {
    \\            mode: Flag = .off,
    \\        };
    \\    }
    \\};
    \\
    \\const Small = Wrap.make(Flag8);
    \\const Large = Wrap.make(Flag32);
;

test "an enum literal default resolves under the container it was reached with" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-enum-default-test.zig", generic_enum_default_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const small = (try analyser.resolveTypeOfNode(.of(try findCall(tree, "make", "Flag8"), handle))).?;
    const large = (try analyser.resolveTypeOfNode(.of(try findCall(tree, "make", "Flag32"), handle))).?;
    try std.testing.expect(small.data == .container);
    try std.testing.expect(large.data == .container);

    // The SAME `.off` node, read under each instantiation.  An enum literal
    // is named against its expected type, and that expected type is this
    // instantiation's own field — so an erased context answers with the
    // other instantiation's tag, or with nothing at all.
    const off = try findEnumLiteral(tree, "off");
    const off_in_small = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(off, handle),
        .container_type = small,
    })) orelse return error.EnumLiteralUnresolved;
    const off_in_large = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(off, handle),
        .container_type = large,
    })) orelse return error.EnumLiteralUnresolved;

    try std.testing.expect(!off_in_small.eql(off_in_large));
}

/// The identifier `name` written anywhere in `tree`.
fn findIdentifier(tree: *const Ast, name: []const u8) error{ IdentifierNotFound }!Ast.Node.Index {
    return findIdentifierFrom(tree, name, 0);
}

/// The identifier `name` written at or after node `from`.  Two containers
/// in one file can declare the same member name, so a second look has to
/// start past the first.
fn findIdentifierFrom(tree: *const Ast, name: []const u8, from: usize) error{ IdentifierNotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (raw < from) continue;
        if (tag != .identifier) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const token = ast.identifierTokenFromIdentifierNode(tree, node) orelse continue;
        if (!std.mem.eql(u8, offsets.identifierTokenToNameSlice(tree, token), name)) continue;
        return node;
    }
    return error.IdentifierNotFound;
}

/// ONE generic function, called with an `@This()`-dependent argument from
/// TWO different containers in the SAME file.
///
/// Same file, so a document-and-module test cannot tell the two apart —
/// only the lexical scope can.  The argument names a member that exists in
/// both containers with a different type, so answering either call site
/// under the wrong container is visible as a wrong answer rather than as
/// a missing one.
const same_file_two_containers_source: [:0]const u8 =
    \\fn probe(context: anytype) void {
    \\    _ = context;
    \\}
    \\
    \\const Alpha = struct {
    \\    const Tag = enum(u8) { a, b };
    \\    pub fn run() void {
    \\        probe(@This().Tag);
    \\    }
    \\};
    \\
    \\const Beta = struct {
    \\    const Tag = enum(u32) { a, b };
    \\    pub fn run() void {
    \\        probe(@This().Tag);
    \\    }
    \\};
;

test "a caller's @This() argument types under its own container, not the other's" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-same-file-two-containers-test.zig", same_file_two_containers_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    // TWO real call sites of the same generic function, one inside each
    // container, in the same file.  A document-and-module test cannot tell
    // them apart at all; only the lexical scope can, which is what makes
    // these the right witnesses.
    const alpha_call = try findCall(tree, "probe", "");
    const beta_call = try findCallFrom(tree, "probe", "", @intFromEnum(alpha_call) + 1);
    try std.testing.expect(alpha_call != beta_call);

    const alpha_ctx = try analyser.innermostContainer(handle, tree.tokenStart(tree.nodeMainToken(alpha_call)));
    const beta_ctx = try analyser.innermostContainer(handle, tree.tokenStart(tree.nodeMainToken(beta_call)));
    try std.testing.expect(!alpha_ctx.eql(beta_ctx));

    // Each call site's OWN argument, read in that call site's OWN frame —
    // exactly what the fallback scan does for a call site whose container
    // IS the frame, and what it must refuse to do for one whose it is not.
    const alpha_arg = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(try callArgument(tree, alpha_call), handle),
        .container_type = alpha_ctx,
    })) orelse return error.CallerArgumentUnresolved;
    const beta_arg = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(try callArgument(tree, beta_call), handle),
        .container_type = beta_ctx,
    })) orelse return error.CallerArgumentUnresolved;

    // `Alpha.Tag` and `Beta.Tag` are both enums and both exist, so an
    // argument answered under the wrong container is a WRONG answer rather
    // than a missing one.  This is the pair that collapses when a container
    // reaches a call site it is not the frame of.
    try std.testing.expect(alpha_arg.is_type_val);
    try std.testing.expect(beta_arg.is_type_val);
    try std.testing.expect(!alpha_arg.eql(beta_arg));
}

test "one formal read under two actual containers answers each" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-formal-container-test.zig", generic_actual_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const byte_ty = (try instantiateCallAt(analyser, handle, tree, try findCall(tree, "make", "u8"), null))
        .data.function.container_type.*;
    const word_ty = (try instantiateCallAt(analyser, handle, tree, try findCall(tree, "make", "u64"), null))
        .data.function.container_type.*;

    // The `T` written inside `make`'s own body.  Resolving it as the
    // DECLARATION it names, under each container, is what the analyser
    // does when any other node in that body reaches the name.
    const t_node = try findIdentifier(tree, "T");
    const t_token = ast.identifierTokenFromIdentifierNode(tree, t_node).?;
    const found = (try analyser.lookupSymbolGlobal(handle, "T", tree.tokenStart(t_token))) orelse
        return error.FormalNotFound;


    const t_in_byte = (try (DeclWithHandle{
        .decl = found.decl,
        .handle = found.handle,
        .container_type = byte_ty,
    }).resolveType(analyser)) orelse return error.FormalUnresolved;
    const t_in_word = (try (DeclWithHandle{
        .decl = found.decl,
        .handle = found.handle,
        .container_type = word_ty,
    }).resolveType(analyser)) orelse return error.FormalUnresolved;

    // One declaration, two actual containers, two concrete answers — and
    // neither of them the container's own unresolved `T`.
    try std.testing.expect(t_in_byte.data == .ip_index);
    try std.testing.expect(t_in_word.data == .ip_index);
    try std.testing.expect(!t_in_byte.eql(t_in_word));

    // One step down inside this declaration keeps BOTH the handle it
    // belongs to and the container it is being read as.
    const stepped = (DeclWithHandle{
        .decl = found.decl,
        .handle = found.handle,
        .container_type = byte_ty,
    }).at(t_node);
    try std.testing.expect(stepped.node_handle.handle.eql(handle));
    try std.testing.expectEqual(@intFromEnum(t_node), @intFromEnum(stepped.node_handle.node));
    try std.testing.expect(stepped.container_type != null);
    try std.testing.expect(stepped.container_type.?.eql(byte_ty));
}

test "a callsite cache key separates parameter, declaration and actual container" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-callsite-key-test.zig", generic_actual_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const param: Declaration.Param = .{ .param_index = 0, .func = try findIdentifier(tree, "T") };
    const other_param: Declaration.Param = .{ .param_index = 1, .func = param.func };
    // Same physical document, different module: `Handle.eql` treats that
    // as a different declaration entirely, so the key must too.
    const other_module_handle: DocumentStore.Handle = .{
        .document = handle.document,
        .module = @enumFromInt(@intFromEnum(handle.module) + 1),
    };
    const byte_ty = (try instantiateCallAt(analyser, handle, tree, try findCall(tree, "make", "u8"), null))
        .data.function.container_type.*;
    const word_ty = (try instantiateCallAt(analyser, handle, tree, try findCall(tree, "make", "u64"), null))
        .data.function.container_type.*;

    const base: CallsiteKey = .{ .param = param, .handle = handle, .container_type = byte_ty };
    const same: CallsiteKey = .{ .param = param, .handle = handle, .container_type = byte_ty };
    const other_actual: CallsiteKey = .{ .param = param, .handle = handle, .container_type = word_ty };
    const other_formal: CallsiteKey = .{ .param = other_param, .handle = handle, .container_type = byte_ty };
    const other_decl: CallsiteKey = .{ .param = param, .handle = other_module_handle, .container_type = byte_ty };
    const no_actual: CallsiteKey = .{ .param = param, .handle = handle, .container_type = null };

    const context = CallsiteKey.Context{};
    // The bare parameter is not an identity: two actuals, two formals and
    // two declarations are three different questions about it.
    try std.testing.expect(context.eql(base, same));
    try std.testing.expect(!context.eql(base, other_actual));
    try std.testing.expect(!context.eql(base, other_formal));
    try std.testing.expect(!context.eql(base, other_decl));
    try std.testing.expect(!context.eql(base, no_actual));
    try std.testing.expect(context.eql(no_actual, no_actual));
    // Equal keys hash equally, or one of them is never found.
    try std.testing.expectEqual(context.hash(base), context.hash(same));
    try std.testing.expect(context.hash(base) != context.hash(other_actual));
    try std.testing.expect(context.hash(base) != context.hash(other_formal));
    try std.testing.expect(context.hash(base) != context.hash(no_actual));
}

/// One generic declaration instantiated twice, read through the ONE field
/// type node both instantiations share.
const generic_actual_context_source: [:0]const u8 =
    \\const Wrap = struct {
    \\    fn make(comptime T: type) type {
    \\        return struct {
    \\            one: T,
    \\        };
    \\    }
    \\};
    \\
    \\const Byte = Wrap.make(u8);
    \\const Word = Wrap.make(u64);
;

test "one declaration read under two actual containers answers each" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-actual-context-test.zig", generic_actual_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const byte_call = try findCall(tree, "make", "u8");
    const byte_ty = (try analyser.resolveTypeOfNode(.of(byte_call, handle))).?;
    try std.testing.expect(byte_ty.is_type_val);
    try std.testing.expect(byte_ty.data == .container);

    // Read the field FIRST, under `u8`.  A node cache keyed on the AST
    // alone — or on anything but the actual container — would answer the
    // `u64` read below with this answer instead of its own.
    const byte_field = (try lookupSymbolContainer(byte_ty, "one", .field)) orelse return error.FieldNotFound;
    const byte_one = (try byte_field.resolveType(analyser)).?;

    const word_call = try findCall(tree, "make", "u64");
    const word_ty = (try analyser.resolveTypeOfNode(.of(word_call, handle))).?;
    try std.testing.expect(word_ty.is_type_val);
    try std.testing.expect(word_ty.data == .container);

    const word_field = (try lookupSymbolContainer(word_ty, "one", .field)) orelse return error.FieldNotFound;
    const word_one = (try word_field.resolveType(analyser)).?;

    // The same `one: T` node, two actual arguments, two answers.  Neither
    // may be the container's own unresolved `T`, and neither may be the
    // other's answer.
    try std.testing.expect(byte_one.data == .ip_index);
    try std.testing.expect(word_one.data == .ip_index);
    try std.testing.expect(!byte_one.eql(word_one));
    try std.testing.expect(!byte_ty.eql(word_ty));

    // One step down is one step down: the same declaration, read under the
    // same actual container.  A step down that dropped either would ask a
    // different question, which is how a container's own context used to
    // disappear one level into a body.
    const frame_start: ResolveOptions = .{ .node_handle = .of(byte_call, handle), .container_type = byte_ty };
    const frame_child: ResolveOptions = frame_start.at(byte_call);
    try std.testing.expect(frame_child.node_handle.handle.eql(handle));
    try std.testing.expectEqual(@intFromEnum(byte_call), @intFromEnum(frame_child.node_handle.node));
    try std.testing.expect(frame_child.container_type != null);
    try std.testing.expect(frame_child.container_type.?.eql(byte_ty));

    // A node resolved without a container still steps down without one.
    try std.testing.expect((ResolveOptions.of(byte_call, handle)).at(byte_call).container_type == null);
}

test "the node cache key separates two actual containers of one declaration" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-node-with-uri-container-key-test.zig", generic_actual_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const byte_ty = (try analyser.resolveTypeOfNode(.of(try findCall(tree, "make", "u8"), handle))).?;
    const word_ty = (try analyser.resolveTypeOfNode(.of(try findCall(tree, "make", "u64"), handle))).?;

    const node = try findCall(tree, "make", "u8");
    const context = NodeWithUri.Context{};
    const in_byte: NodeWithUri = .{
        .node = node,
        .uri = handle.document.uri,
        .module = handle.module,
        .container_type = byte_ty,
    };
    const in_byte_again: NodeWithUri = .{ .node = node, .uri = handle.document.uri, .module = handle.module, .container_type = byte_ty };
    const in_word: NodeWithUri = .{ .node = node, .uri = handle.document.uri, .module = handle.module, .container_type = word_ty };
    const no_container: NodeWithUri = .{ .node = node, .uri = handle.document.uri, .module = handle.module };

    // Two instantiations of ONE declaration are two questions.
    try std.testing.expect(!context.eql(in_byte, in_word));
    // One instantiation asked twice is the same question, and must hash so.
    try std.testing.expect(context.eql(in_byte, in_byte_again));
    // A question with no container is not a question about some container.
    try std.testing.expect(!context.eql(in_byte, no_container));
    try std.testing.expect(context.eql(no_container, no_container));
    // Equal keys hash equally — otherwise one of them is never found.
    try std.testing.expectEqual(context.hash(in_byte), context.hash(in_byte_again));
    try std.testing.expect(context.hash(in_byte) != context.hash(in_word));
    try std.testing.expect(context.hash(in_byte) != context.hash(no_container));
}

/// ONE generic function, an `anytype` context parameter, reached with two
/// different actual contexts.  There is no container under test here: the
/// binding lives on the function itself, and the question is whether the
/// metadata it carries reaches the nested `context.read()` in its body.
const generic_anytype_context_source: [:0]const u8 =
    \\fn invoke(context: anytype) void {
    \\    _ = context.read();
    \\}
    \\
    \\const Bytes = struct {
    \\    value: u8,
    \\    pub fn read(self: Bytes) u8 {
    \\        return self.value;
    \\    }
    \\};
    \\
    \\const Words = struct {
    \\    value: u32,
    \\    pub fn read(self: Words) u32 {
    \\        return self.value;
    \\    }
    \\};
    \\
    \\const bytes: Bytes = .{ .value = 1 };
    \\const words: Words = .{ .value = 2 };
    \\
    \\fn fromBytes() void {
    \\    invoke(bytes);
    \\}
    \\
    \\fn fromWords() void {
    \\    invoke(words);
    \\}
;

test "one anytype function bound to two contexts resolves its nested callback under each" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-anytype-context-test.zig", generic_anytype_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const bytes_call = try findCall(tree, "invoke", "bytes");
    const words_call = try findCall(tree, "invoke", "words");
    const nested = try findCall(tree, "read", "");

    const from_bytes = try instantiateCallAt(analyser, handle, tree, bytes_call, null);
    const from_words = try instantiateCallAt(analyser, handle, tree, words_call, null);

    // The SAME function, reached twice, now carries two different actual
    // contexts.  A binding the function does not publish is a binding the
    // engine cannot read anywhere, so this is the metadata install.
    try std.testing.expect(!from_bytes.data.function.container_type.*.eql(
        from_words.data.function.container_type.*,
    ));

    // Read the ONE `context.read()` node under each of them.  Before the
    // bindings were published this node had no way to name either context:
    // `context` stayed an `anytype` parameter and the nested call resolved
    // to nothing at all, or to whichever call was seen first.
    const read_in_bytes = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(nested, handle),
        .container_type = from_bytes.data.function.container_type.*,
    })) orelse return error.NestedCallbackUnresolved;
    const read_in_words = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(nested, handle),
        .container_type = from_words.data.function.container_type.*,
    })) orelse return error.NestedCallbackUnresolved;

    // `Bytes.read` returns `u8` and `Words.read` returns `u32`: the nested
    // callback resolved under the context it was actually reached with.
    try std.testing.expect(!read_in_bytes.eql(read_in_words));
}

test "an anytype formal resolves to the actual argument's value, not its type" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-anytype-formal-value-test.zig", generic_anytype_context_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const context_node = try findIdentifier(tree, "context");
    const context_token = ast.identifierTokenFromIdentifierNode(tree, context_node).?;
    const found = (try analyser.lookupSymbolGlobal(handle, "context", tree.tokenStart(context_token))) orelse
        return error.FormalNotFound;

    const read_under = struct {
        fn go(a: *Analyser, h: DocumentStore.Handle, t: *const Ast, decl: DeclWithHandle, arg: []const u8) !Type {
            const published = (try instantiateCallAt(a, h, t, try findCall(t, "invoke", arg), null))
                .data.function.container_type.*;
            const bound = DeclWithHandle{
                .decl = decl.decl,
                .handle = decl.handle,
                .container_type = published,
            };
            return (try bound.resolveType(a)) orelse return error.FormalUnresolved;
        }
    }.go;

    const context_in_bytes = try read_under(analyser, handle, tree, found, "bytes");
    const context_in_words = try read_under(analyser, handle, tree, found, "words");

    // The formal holds a VALUE of the argument's type — not the type itself.
    // `is_type_val` is what says so, and it is the distinction that matters:
    // the body reads `context.read()` off an instance.
    //
    // The DATA variant is deliberately NOT asserted.  `bytes` is a struct
    // instance, which this engine legitimately carries as `.container`; an
    // `.ip_index` spelling would pin an internal representation without
    // saying anything about the value.  What must hold is that the two
    // instantiations hold two DIFFERENT actuals, asserted below.
    try std.testing.expect(!context_in_bytes.is_type_val);
    try std.testing.expect(!context_in_words.is_type_val);

    // One formal, two instantiations, two different argument values.
    try std.testing.expect(!context_in_bytes.eql(context_in_words));
}

/// ONE `anytype` formal called with two TYPE VALUES.  `Reading` and
/// `Writing` are both types, so "the type of the argument" is `type_type`
/// for each — a binding that stores only that collapses two different
/// actuals into one.
const generic_anytype_type_value_source: [:0]const u8 =
    \\const Reading = struct {
    \\    pub fn read() u8 {
    \\        return 1;
    \\    }
    \\};
    \\
    \\const Writing = struct {
    \\    pub fn read() u64 {
    \\        return 2;
    \\    }
    \\};
    \\
    \\fn invoke(comptime Context: anytype) void {
    \\    _ = Context.read();
    \\}
    \\
    \\fn fromReading() void {
    \\    invoke(Reading);
    \\}
    \\
    \\fn fromWriting() void {
    \\    invoke(Writing);
    \\}
;

test "an anytype formal bound to two type values keeps both actuals distinct" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-anytype-type-value-test.zig", generic_anytype_type_value_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const nested = try findCall(tree, "read", "");
    const reading = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "invoke", "Reading"), null);
    const writing = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "invoke", "Writing"), null);

    // Two actual types bound to ONE formal.  Both arguments are types, so a
    // binding holding only "the type of the argument" is `type_type` twice
    // and the two instantiations collapse into one.
    try std.testing.expect(!reading.data.function.container_type.*.eql(
        writing.data.function.container_type.*,
    ));

    // The nested static callback each one reaches through the formal.
    const read_in_reading = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(nested, handle),
        .container_type = reading.data.function.container_type.*,
    })) orelse return error.NestedCallbackUnresolved;
    const read_in_writing = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(nested, handle),
        .container_type = writing.data.function.container_type.*,
    })) orelse return error.NestedCallbackUnresolved;
    try std.testing.expect(!read_in_reading.eql(read_in_writing));

    // The formal itself.  The argument IS a type value, so the formal
    // holds a type value — the flags the call passed, not a flag this
    // engine chose to suit itself.
    const context_node = try findIdentifier(tree, "Context");
    const context_token = ast.identifierTokenFromIdentifierNode(tree, context_node).?;
    const found = (try analyser.lookupSymbolGlobal(handle, "Context", tree.tokenStart(context_token))) orelse
        return error.FormalNotFound;

    const ctx_in_reading = (try (DeclWithHandle{
        .decl = found.decl,
        .handle = found.handle,
        .container_type = reading.data.function.container_type.*,
    }).resolveType(analyser)) orelse return error.FormalUnresolved;
    const ctx_in_writing = (try (DeclWithHandle{
        .decl = found.decl,
        .handle = found.handle,
        .container_type = writing.data.function.container_type.*,
    }).resolveType(analyser)) orelse return error.FormalUnresolved;

    try std.testing.expect(ctx_in_reading.is_type_val);
    try std.testing.expect(ctx_in_writing.is_type_val);
    try std.testing.expect(!ctx_in_reading.eql(ctx_in_writing));
}


/// The builtin call `@name(…, arg_text, …)` written anywhere in `tree`.
/// `arg_index` may exceed the argument count, which simply never matches.
fn findBuiltinArg(tree: *const Ast, name: []const u8, arg_index: usize, arg_text: []const u8) error{ NotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node) orelse continue;
        if (arg_text.len == 0) return node;
        if (arg_index >= params.len) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.firstToken(params[arg_index])), arg_text)) continue;
        return node;
    }
    return error.NotFound;
}

/// A `comptime` formal bound to a string literal, reached by reading that
/// formal by name.  `@field(value, "name")` is deliberately NOT in here:
/// it evaluates to the selected field's VALUE, not to a name, so a string
/// reader that echoed its name argument would be a mock.
const bound_string_literal_source: [:0]const u8 =
    \\fn label(comptime name: []const u8) void {
    \\    _ = name;
    \\}
    \\fn useKey() void {
    \\    label("key");
    \\}
    \\fn useValue() void {
    \\    label("value");
    \\}
;

test "a comptime string formal binds its bytes for the frame that supplied it" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-bound-string-value-test.zig", bound_string_literal_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const in_key = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "label", "\"key\""), null);
    const in_value = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "label", "\"value\""), null);

    // Two strings on ONE formal: two instantiations, two actuals.
    try std.testing.expect(!in_key.data.function.container_type.*.eql(
        in_value.data.function.container_type.*,
    ));

    const name_node = try findIdentifier(tree, "name");
    const key_bytes = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(name_node, handle),
        .container_type = in_key.data.function.container_type.*,
    })) orelse return error.StringFormalUnresolved;
    const value_bytes = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(name_node, handle),
        .container_type = in_value.data.function.container_type.*,
    })) orelse return error.StringFormalUnresolved;

    try std.testing.expectEqualStrings("key", key_bytes);
    try std.testing.expectEqualStrings("value", value_bytes);
}

/// The call `callee(.<tag>, …)` written anywhere in `tree` — matched on
/// the TAG, not on the punctuation, which `firstToken` may or may not
/// include.
fn findCallOnEnumTag(tree: *const Ast, callee: []const u8, tag: []const u8) error{ CallNotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |node_tag, raw| {
        switch (node_tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), callee)) continue;
        if (call.ast.params.len == 0) continue;
        if (tree.nodeTag(call.ast.params[0]) != .enum_literal) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(call.ast.params[0])), tag)) continue;
        return node;
    }
    return error.CallNotFound;
}

/// A `comptime` formal that is an ENUM TAG, reached through `@tagName` —
/// the shape `Slice.items(self, comptime field: Field) []FieldType(field)`
/// has in the pinned SDK, where the tag's NAME is what `@FieldType` needs.
const bound_enum_tag_source: [:0]const u8 =
    \\const Field = enum { key, value };
    \\fn take(comptime field: Field) void {
    \\    _ = @tagName(field);
    \\}
    \\fn useKey() void {
    \\    take(.key);
    \\}
    \\fn useValue() void {
    \\    take(.value);
    \\}
;

test "an enum tag formal binds its tag name for @tagName" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-bound-enum-tag-test.zig", bound_enum_tag_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const tag_name = try findBuiltinArg(tree, "@tagName", 0, "field");
    const in_key = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "key"), null);
    const in_value = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "value"), null);

    // Two tags on ONE formal: two instantiations, two actuals.
    try std.testing.expect(!in_key.data.function.container_type.*.eql(
        in_value.data.function.container_type.*,
    ));

    const key_name = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(tag_name, handle),
        .container_type = in_key.data.function.container_type.*,
    })) orelse return error.TagNameUnresolved;
    const value_name = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(tag_name, handle),
        .container_type = in_value.data.function.container_type.*,
    })) orelse return error.TagNameUnresolved;

    try std.testing.expectEqualStrings("key", key_name);
    try std.testing.expectEqualStrings("value", value_name);
}

/// A `comptime` BOOLEAN formal: the two arguments are two instantiations,
/// not one instantiation read twice.
const bound_bool_source: [:0]const u8 =
    \\fn pick(comptime flag: bool) void {
    \\    _ = flag;
    \\}
    \\fn on() void {
    \\    pick(true);
    \\}
    \\fn off() void {
    \\    pick(false);
    \\}
;

test "a comptime bool formal binds the argument's actual value" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-bound-bool-test.zig", bound_bool_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const on_call = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "pick", "true"), null);
    const off_call = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "pick", "false"), null);

    // Two booleans on ONE formal.  If the binder only understood integers,
    // both would carry nothing and the two would be the same function.
    try std.testing.expect(!on_call.data.function.container_type.*.eql(
        off_call.data.function.container_type.*,
    ));

    const flag_node = try findIdentifier(tree, "flag");
    const flag_token = ast.identifierTokenFromIdentifierNode(tree, flag_node).?;
    const found = (try analyser.lookupSymbolGlobal(handle, "flag", tree.tokenStart(flag_token))) orelse
        return error.FormalNotFound;

    const read_under = struct {
        fn go(a: *Analyser, decl: DeclWithHandle, call_ty: Type) !Type {
            const bound = DeclWithHandle{
                .decl = decl.decl,
                .handle = decl.handle,
                .container_type = call_ty.data.function.container_type.*,
            };
            return (try bound.resolveType(a)) orelse return error.FormalUnresolved;
        }
    }.go;

    const when_on = try read_under(analyser, found, on_call);
    const when_off = try read_under(analyser, found, off_call);

    // A boolean argument binds a VALUE, so the formal answers a value and
    // not a type value — and the two differ.
    try std.testing.expect(!when_on.is_type_val);
    try std.testing.expect(!when_off.is_type_val);
    try std.testing.expect(!when_on.eql(when_off));
}

/// A `comptime` formal whose DECLARED type this engine cannot read as an
/// enum, standing in for `meta.FieldEnum(Elem)` — an `@Enum` synthesized
/// over a type, with no AST behind it and no enum type to resolve.  The
/// argument is a literal, so the tag is known even though the declared
/// type is not.
const unknown_enum_formal_source: [:0]const u8 =
    \\fn take(comptime field: []const u8) void {
    \\    _ = @tagName(field);
    \\}
    \\fn useKey() void {
    \\    take(.key);
    \\}
    \\fn useValue() void {
    \\    take(.value);
    \\}
;

test "a literal enum tag binds even when the declared type is not a readable enum" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-unknown-enum-formal-test.zig", unknown_enum_formal_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const tag_name = try findBuiltinArg(tree, "@tagName", 0, "field");
    const in_key = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "key"), null);
    const in_value = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "value"), null);

    try std.testing.expect(!in_key.data.function.container_type.*.eql(
        in_value.data.function.container_type.*,
    ));

    const key_name = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(tag_name, handle),
        .container_type = in_key.data.function.container_type.*,
    })) orelse return error.TagNameUnresolved;
    const value_name = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(tag_name, handle),
        .container_type = in_value.data.function.container_type.*,
    })) orelse return error.TagNameUnresolved;

    // The literal is the proof; the declared type is not required.
    try std.testing.expectEqualStrings("key", key_name);
    try std.testing.expectEqualStrings("value", value_name);
}

/// THREE functions in one file: a literal tag enters at `take`, is handed
/// to `middle` BY NAME — the forwarding seam — and `middle` reads it back.
const forwarded_enum_source: [:0]const u8 =
    \\fn middle(comptime field: []const u8) void {
    \\    _ = @tagName(field);
    \\}
    \\fn take(comptime field: []const u8) void {
    \\    middle(field);
    \\}
    \\fn useKey() void {
    \\    take(.key);
    \\}
    \\fn useValue() void {
    \\    take(.value);
    \\}
;

test "a bound enum tag forwards through a middle function by name" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-forwarded-enum-value-test.zig", forwarded_enum_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const tag_name = try findBuiltinArg(tree, "@tagName", 0, "field");
    const in_key = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "key"), null);
    const in_value = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "value"), null);

    // Two tags, one formal, two full identities.
    try std.testing.expect(!in_key.data.function.container_type.*.eql(
        in_value.data.function.container_type.*,
    ));
    // `middle`'s OWN `@tagName(field)` lives in a DIFFERENT function, under a
    // DIFFERENT `field` token, and `take`'s frame cannot answer for it: one
    // caller frame cannot say which tag it gave `middle`.  So the call that
    // really exists — `middle(field)`, written inside `take` — is instantiated
    // once per `take` frame, and `middle`'s body is read under the frame that
    // call published.  The transfer is the production one, under production
    // rules: `take`'s binding, forwarded by name.
    const middle_call = try findCall(tree, "middle", "field");
    const middle_in_key = try instantiateCallAtInFrame(
        analyser,
        handle,
        tree,
        middle_call,
        null,
        in_key.data.function.container_type.*,
    );
    const middle_in_value = try instantiateCallAtInFrame(
        analyser,
        handle,
        tree,
        middle_call,
        null,
        in_value.data.function.container_type.*,
    );

    // Two callers, two actuals: the two `middle` instantiations are two
    // identities even though `middle` is one function written once.
    try std.testing.expect(!middle_in_key.data.function.container_type.*.eql(
        middle_in_value.data.function.container_type.*,
    ));

    const key_name = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(tag_name, handle),
        .container_type = middle_in_key.data.function.container_type.*,
    })) orelse return error.ForwardedTagUnresolved;
    const value_name = (try analyser.resolveStringLiteral(.{
        .node_handle = .of(tag_name, handle),
        .container_type = middle_in_value.data.function.container_type.*,
    })) orelse return error.ForwardedTagUnresolved;

    try std.testing.expectEqualStrings("key", key_name);
    try std.testing.expectEqualStrings("value", value_name);
}

/// The pinned SDK's own chain: `Self.items(.value)` -> `self.slice()
/// .items(field)` -> `[]FieldType(field)`, where `FieldType` is
/// `@FieldType(Elem, @tagName(field))`.  The tag enters as a literal, is
/// forwarded BY NAME, and the SELECTED FIELD decides a return type — so the
/// two actuals differ in the WIDTH of what they return.
const forwarded_field_type_source: [:0]const u8 =
    \\const Elem = struct {
    \\    key: u8,
    \\    value: u64,
    \\};
    \\fn FieldType(comptime field: []const u8) type {
    \\    return @FieldType(Elem, @tagName(field));
    \\}
    \\fn items(comptime field: []const u8) []FieldType(field) {
    \\    return &.{};
    \\}
    \\fn middle(comptime field: []const u8) []FieldType(field) {
    \\    return items(field);
    \\}
    \\fn take(comptime field: []const u8) []FieldType(field) {
    \\    return middle(field);
    \\}
    \\fn useKey() void {
    \\    _ = take(.key);
    \\}
    \\fn useValue() void {
    \\    _ = take(.value);
    \\}
;

test "a forwarded tag selects the field type a call returns" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-forwarded-field-type-test.zig", forwarded_field_type_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const in_key = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "key"), null);
    const in_value = try instantiateCallAt(analyser, handle, tree, try findCallOnEnumTag(tree, "take", "value"), null);

    const key_return = in_key.data.function.return_value.*;
    const value_return = in_value.data.function.return_value.*;

    // `[]FieldType(field)` for `key` is `[]u8` and for `value` is `[]u64`.
    // Comparing the two return types is NOT enough: two distinct bindings
    // can sit on two equally unknown children and still differ.  This
    // reads the SLICE and then its ELEMENT's width, which is the thing
    // `@FieldType` actually selected.
    const child_bits = struct {
        fn go(a: *Analyser, slice_ty: Type) !u16 {
            const info = switch (slice_ty.data) {
                .pointer => |info| info,
                else => return error.NotASlice,
            };
            try std.testing.expectEqual(std.builtin.Type.Pointer.Size.slice, info.size);
            const child = info.elem_ty.*;
            // Whether the element is flagged as a type value is an internal
            // representation choice — `[]u8`'s element is legitimately
            // carried either way — and says nothing about the width
            // `@FieldType` actually selected.  What must hold is that the
            // element IS an unsigned int of the right width, asserted below.
            const index = child.ipIndex() orelse return error.UnknownChild;
            const int_info = switch (a.ip.indexToKey(index)) {
                .int_type => |int| int,
                else => return error.ChildNotAnInt,
            };
            try std.testing.expectEqual(std.builtin.Signedness.unsigned, int_info.signedness);
            return int_info.bits;
        }
    }.go;

    try std.testing.expectEqual(@as(u16, 8), try child_bits(analyser, key_return));
    try std.testing.expectEqual(@as(u16, 64), try child_bits(analyser, value_return));
}

/// A `switch` whose SELECTOR is a `comptime` formal of the function: the
/// selector is only a constant when the frame this call site published is
/// the one being read, and each prong's own values are read the same way.
const generic_switch_source: [:0]const u8 =
    \\fn pick(comptime n: u32) u32 {
    \\    return switch (n) {
    \\        1 => 10,
    \\        2 => 20,
    \\        else => 0,
    \\    };
    \\}
    \\fn one() u32 {
    \\    return pick(1);
    \\}
    \\fn two() u32 {
    \\    return pick(2);
    \\}
;

/// The `switch` expression written anywhere in `tree`.
fn findSwitch(tree: *const Ast) error{ NotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .@"switch", .switch_comma => {},
            else => continue,
        }
        return @enumFromInt(raw);
    }
    return error.NotFound;
}

test "a switch over a bound comptime selector narrows under its own frame" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-generic-switch-narrowing-test.zig", generic_switch_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const switch_node = try findSwitch(tree);
    const in_one = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "pick", "1"), null);
    const in_two = try instantiateCallAt(analyser, handle, tree, try findCall(tree, "pick", "2"), null);

    // The SAME switch node, read under each call's own published frame.  A
    // narrowing that read the selector without the frame would leave it
    // unknown and answer the same conservative Either for both.
    const narrowed_one = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(switch_node, handle),
        .container_type = in_one.data.function.container_type.*,
    })) orelse return error.SwitchUnresolved;
    const narrowed_two = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(switch_node, handle),
        .container_type = in_two.data.function.container_type.*,
    })) orelse return error.SwitchUnresolved;

    try std.testing.expect(narrowed_one.data == .ip_index);
    try std.testing.expect(narrowed_two.data == .ip_index);
    try std.testing.expect(!narrowed_one.eql(narrowed_two));

    // A -> B -> A: reading the other frame in between must not leave the
    // first one's answer behind.  The node cache is keyed on the whole
    // question, so the second read of `pick(1)` is a different key and has
    // to answer for itself.
    const one_again = (try analyser.resolveTypeOfNode(.{
        .node_handle = .of(switch_node, handle),
        .container_type = in_one.data.function.container_type.*,
    })) orelse return error.SwitchUnresolved;
    try std.testing.expect(one_again.eql(narrowed_one));
    try std.testing.expect(!one_again.eql(narrowed_two));

    // The BASELINE: with no frame at all the selector is an unbound
    // formal, so nothing may narrow and the answer must be the conservative
    // one that matches NEITHER prong.
    const unframed = (try analyser.resolveTypeOfNode(.of(switch_node, handle))) orelse
        return error.SwitchUnresolved;
    try std.testing.expect(!unframed.eql(narrowed_one));
    try std.testing.expect(!unframed.eql(narrowed_two));
}

/// The comparison of two integer CONSTANTS: the shape `@sizeOf(T) == 0`
/// has, and the only way a comptime branch on a layout question is decided
/// rather than left as a type.
const integer_comparison_source: [:0]const u8 =
    \\fn truth() bool {
    \\    return 1 == 1;
    \\}
    \\fn lies() bool {
    \\    return 1 == 2;
    \\}
    \\fn neq() bool {
    \\    return 8 != 0;
    \\}
    \\fn unknownSide() bool {
    \\    return someUnresolved() == 0;
    \\}
;

/// The comparison expression written anywhere in `tree`.
fn findComparison(tree: *const Ast) error{ NotFound }!Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .equal_equal, .bang_equal => {},
            else => continue,
        }
        return @enumFromInt(raw);
    }
    return error.NotFound;
}

test "two integer constants decide a comparison; an unresolved side does not" {
    const gpa = std.testing.allocator;
    const fixture = try AnalyserFixture.create(gpa, "zbc-integer-comparison-test.zig", integer_comparison_source);
    defer fixture.destroy(gpa);
    const analyser = &fixture.analyser;
    const handle = fixture.handle;
    const tree = fixture.tree();

    const comparisons = struct {
        var found: [3]Ast.Node.Index = undefined;
        var count: usize = 0;
        fn go(t: *const Ast) void {
            for (t.nodes.items(.tag), 0..) |tag, raw| {
                switch (tag) {
                    .equal_equal, .bang_equal => {},
                    else => continue,
                }
                if (count < found.len) {
                    found[count] = @enumFromInt(raw);
                    count += 1;
                }
            }
        }
    };
    comparisons.go(tree);
    try std.testing.expectEqual(@as(usize, 3), comparisons.count);

    const is_true = struct {
        fn go(a: *Analyser, h: DocumentStore.Handle, n: Ast.Node.Index) !bool {
            const ty = (try a.resolveTypeOfNode(.of(n, h))) orelse return false;
            const index = ty.ipIndex() orelse return false;
            // The comparison answers the interned VALUE it decided, and
            // `.bool_true` is a simple_value.  `typeOf` on any index answers
            // a TYPE — `.bool_true` maps to `.bool_type` — so asking it for
            // a value could never be true, and a correctly decided
            // comparison read as undecided.  The decision IS the value
            // index.
            return index == .bool_true;
        }
    }.go;

    // `1 == 1` and `8 != 0` are both TRUE, `1 == 2` is FALSE.  In source
    // order that is comparisons[0], [2] and [1].
    try std.testing.expect(try is_true(analyser, handle, comparisons.found[0]));
    try std.testing.expect(!try is_true(analyser, handle, comparisons.found[1]));
    try std.testing.expect(try is_true(analyser, handle, comparisons.found[2]));

    // The fourth comparison names a function this document never declares,
    // so neither side is a constant: it must NOT be answered as a boolean.
    const undecided = try findComparison(tree);
    try std.testing.expect(undecided == comparisons.found[0]);
}

/// Returns whether the given `node` is the identifier `type`.
pub fn isMetaType(tree: *const Ast, node: Ast.Node.Index) bool {
    if (tree.nodeTag(node) == .identifier) {
        return std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "type");
    }
    return false;
}

/// Returns whether the given function returns a `type`.
pub fn isTypeFunction(tree: *const Ast, func: Ast.full.FnProto) bool {
    const return_type = func.ast.return_type.unwrap() orelse return false;
    return isMetaType(tree, return_type);
}

// ANALYSIS ENGINE

/// Resolves variable declarations consisting of chains of imports and field accesses of containers
/// Examples:
///```zig
/// const decl = @import("decl-file.zig").decl;
/// const other = decl.middle.other;
///```
pub fn resolveVarDeclAlias(analyser: *Analyser, decl: DeclWithHandle) Error!?DeclWithHandle {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const initial_node = switch (decl.decl) {
        .ast_node => |node| node,
        else => return null,
    };

    var node_trail: NodeSet = .empty;
    defer node_trail.deinit(analyser.gpa);

    var current: ResolveOptions = .{
        .node_handle = .of(initial_node, decl.handle),
        .container_type = decl.container_type,
    };
    var result: ?DeclWithHandle = null;
    while (true) {
        const node = current.node_handle.node;
        const handle = current.node_handle.handle;
        const tree = &handle.document.tree;

        const resolved: DeclWithHandle = switch (tree.nodeTag(node)) {
            .identifier => blk: {
                const name_token = ast.identifierTokenFromIdentifierNode(tree, node) orelse break :blk null;
                const name = offsets.identifierTokenToNameSlice(tree, name_token);
                if (current.container_type) |ty| {
                    break :blk try ty.lookupSymbol(analyser, name);
                }
                break :blk try analyser.lookupSymbolGlobal(
                    handle,
                    name,
                    tree.tokenStart(name_token),
                );
            },
            .field_access => blk: {
                const lhs, const field_name = tree.nodeData(node).node_and_token;
                const resolved = (try analyser.resolveTypeOfNode(.{
                    .node_handle = .of(lhs, handle),
                    .container_type = current.container_type,
                })) orelse break :blk null;
                if (!resolved.is_type_val)
                    break :blk null;

                const symbol_name = offsets.identifierTokenToNameSlice(tree, field_name);

                break :blk try resolved.lookupSymbol(analyser, symbol_name);
            },
            .global_var_decl,
            .local_var_decl,
            .aligned_var_decl,
            .simple_var_decl,
            => {
                const var_decl = tree.fullVarDecl(node).?;

                const base_exp = var_decl.ast.init_node.unwrap() orelse return result;
                if (tree.tokenTag(var_decl.ast.mut_token) != .keyword_const) return result;

                const gop = try node_trail.getOrPut(analyser.gpa, .{ .node = base_exp, .uri = handle.document.uri, .module = handle.module, .comptime_values = analyser.comptime_values, .container_type = current.container_type });
                if (gop.found_existing) return null;

                current.node_handle.node = base_exp;
                continue;
            },
            else => null,
        } orelse return result;

        const resolved_node = switch (resolved.decl) {
            .ast_node => |resolved_node| resolved_node,
            else => return resolved,
        };

        const gop = try node_trail.getOrPut(analyser.gpa, .{ .node = resolved_node, .uri = resolved.handle.document.uri, .module = resolved.handle.module, .comptime_values = analyser.comptime_values, .container_type = resolved.container_type });
        if (gop.found_existing) return null;

        current = .{
            .node_handle = .of(resolved_node, resolved.handle),
            .container_type = resolved.container_type,
        };
        result = resolved;
    }
}

/// resolves `@field(lhs, field_name)`
pub fn resolveFieldAccess(analyser: *Analyser, lhs: Type, field_name: []const u8) Error!?Type {
    const binding = try analyser.resolveFieldAccessBinding(.{ .type = lhs, .is_const = false }, field_name) orelse return null;
    return binding.type;
}

pub fn resolveFieldAccessBinding(analyser: *Analyser, lhs_binding: Binding, field_name: []const u8) Error!?Binding {
    const lhs = lhs_binding.type;

    if (try analyser.resolveUnionTagAccess(lhs, field_name)) |t|
        return .{ .type = t, .is_const = true };

    // If we are accessing a pointer type, remove one pointerness level :)
    const left_type = (try analyser.resolveDerefType(lhs)) orelse lhs;

    if (try analyser.resolvePropertyType(left_type, field_name)) |t|
        return .{
            .type = t,
            .is_const = lhs_binding.is_const,
        };

    if (try left_type.lookupSymbol(analyser, field_name)) |child|
        return .{
            .type = try child.resolveType(analyser) orelse return null,
            .is_const = if (left_type.is_type_val) child.isConst() else lhs_binding.is_const,
        };

    return null;
}

pub fn resolveGenericType(analyser: *Analyser, ty: Type, bound_params: TokenToTypeMap) error{OutOfMemory}!Type {
    var visiting: Type.Data.GenericSet = .empty;
    defer visiting.deinit(analyser.gpa);
    return analyser.resolveGenericTypeInternal(ty, bound_params, &visiting);
}

fn resolveGenericTypeInternal(
    analyser: *Analyser,
    ty: Type,
    bound_params: TokenToTypeMap,
    visiting: *Type.Data.GenericSet,
) error{OutOfMemory}!Type {
    if (!ty.data.isGeneric()) return ty;
    var resolved = ty;
    if (!ty.is_type_val) {
        resolved = try resolved.typeOf(analyser);
    }
    std.debug.assert(resolved.is_type_val);
    resolved.data = try resolved.data.resolveGeneric(analyser, bound_params, visiting);
    if (!ty.is_type_val) {
        resolved = try resolved.instanceUnchecked(analyser);
    }
    return resolved;
}

fn findReturnStatementInternal(tree: *const Ast, body: Ast.Node.Index, already_found: *bool) ?Ast.Node.Index {
    var result: ?Ast.Node.Index = null;

    var buffer: [2]Ast.Node.Index = undefined;
    const statements = tree.blockStatements(&buffer, body) orelse return null;

    for (statements) |child_idx| {
        if (tree.nodeTag(child_idx) == .@"return") {
            if (already_found.*) return null;
            already_found.* = true;
            result = child_idx;
            continue;
        }

        result = findReturnStatementInternal(tree, child_idx, already_found);
    }

    return result;
}

fn findReturnStatement(tree: *const Ast, body: Ast.Node.Index) ?Ast.Node.Index {
    var already_found = false;
    return findReturnStatementInternal(tree, body, &already_found);
}

/// if `func_type_param` is callable, returns an instance of the return type.
/// otherwise, returns null.
pub fn resolveReturnType(analyser: *Analyser, func_type_param: Type) error{OutOfMemory}!?Type {
    const func_type = try analyser.resolveFuncProtoOfCallable(func_type_param) orelse return null;
    const info = func_type.data.function;
    return info.return_value.*;
}

fn resolveReturnValueOfFuncNode(
    analyser: *Analyser,
    handle: DocumentStore.Handle,
    func_node: Ast.Node.Index,
) Error!?Type {
    const tree = &handle.document.tree;

    var buf: [1]Ast.Node.Index = undefined;
    const fn_proto = tree.fullFnProto(&buf, func_node).?;
    const has_body = tree.nodeTag(func_node) == .fn_decl;

    if (isTypeFunction(tree, fn_proto)) {
        if (!has_body) return .unknown_type;
        const body = tree.nodeData(func_node).node_and_node[1];
        // If this is a type function and it only contains a single return statement that returns
        // a container declaration, we will return that declaration.
        const return_node = findReturnStatement(tree, body) orelse return .unknown_type;
        if (tree.nodeData(return_node).opt_node.unwrap()) |return_expr| {
            return try analyser.resolveTypeOfNodeInternal(.of(return_expr, handle)) orelse .unknown_type;
        }

        return .unknown_type;
    }

    const return_type = fn_proto.ast.return_type.unwrap() orelse return null;
    const child_type = (try analyser.resolveTypeOfNodeInternal(.of(return_type, handle))) orelse
        return null;
    if (!child_type.is_type_val) return null;

    if (ast.hasInferredError(tree, fn_proto)) {
        const ty = try Type.createErrorUnionType(analyser, null, child_type);
        return try ty.instanceUnchecked(analyser);
    }

    return try child_type.instanceTypeVal(analyser);
}

/// `optional.?`
pub fn resolveOptionalUnwrap(analyser: *Analyser, optional: Type) error{OutOfMemory}!?Type {
    if (optional.is_type_val) return null;

    // TODO: some uses of this function don't expect C pointers to be unwrapped
    switch (optional.data) {
        .optional => |child_ty| return try child_ty.instanceUnchecked(analyser),
        .pointer => |ptr| {
            if (ptr.size == .c) return optional;
            return null;
        },
        .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
            .optional_type => |optional_info| return Type.fromIP(analyser, optional_info.payload_type, null),
            .pointer_type => |pointer_info| {
                if (pointer_info.flags.size == .c) return optional;
                return null;
            },
            else => return null,
        },
        else => return null,
    }
}

pub fn resolveOrelseType(analyser: *Analyser, lhs: Type, rhs: Type) error{OutOfMemory}!?Type {
    if (rhs.is_type_val) return null;
    return switch (rhs.data) {
        .optional => rhs,
        .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
            .optional_type => rhs,
            else => try analyser.resolveOptionalUnwrap(lhs),
        },
        else => try analyser.resolveOptionalUnwrap(lhs),
    };
}

pub fn resolveAddressOf(analyser: *Analyser, is_const: bool, ty: Type) error{OutOfMemory}!Type {
    const elem_ty = try ty.typeOf(analyser);
    const pointer_ty = try Type.createPointerType(analyser, .one, .none, is_const, elem_ty);
    return try pointer_ty.instanceUnchecked(analyser);
}

pub const ErrorUnionSide = enum { error_set, payload };

pub fn resolveUnwrapErrorUnionType(analyser: *Analyser, ty: Type, side: ErrorUnionSide) error{OutOfMemory}!?Type {
    if (ty.is_type_val) return null;

    return switch (ty.data) {
        .error_union => |info| switch (side) {
            .error_set => try (info.error_set orelse return null).instanceTypeVal(analyser),
            .payload => try info.payload.instanceTypeVal(analyser),
        },
        .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
            .error_union_type => |error_union_info| switch (side) {
                .error_set => {
                    if (error_union_info.error_set_type == .none) return null;
                    return Type.fromIP(analyser, error_union_info.error_set_type, null);
                },
                .payload => return Type.fromIP(analyser, error_union_info.payload_type, null),
            },
            else => return null,
        },
        else => return null,
    };
}

fn resolveUnionTag(analyser: *Analyser, ty: Type) Error!?Type {
    if (!ty.is_type_val)
        return null;

    if (!ty.isTaggedUnion())
        return null;

    const scope_handle = switch (ty.data) {
        .container => |info| info.scope_handle,
        else => return null,
    };
    const node = scope_handle.toNode();
    const handle = scope_handle.handle;

    var buf: [2]Ast.Node.Index = undefined;
    const container_decl = handle.document.tree.fullContainerDecl(&buf, node) orelse
        return null;

    if (container_decl.ast.enum_token != null)
        return .{ .data = .{ .union_tag = try analyser.allocType(ty) }, .is_type_val = false };

    if (container_decl.ast.arg.unwrap()) |arg| {
        const tag_type = (try analyser.resolveTypeOfNode(.of(arg, handle))) orelse return null;
        return try tag_type.instanceTypeVal(analyser) orelse return null;
    }

    return null;
}

fn resolveUnionTagAccess(analyser: *Analyser, ty: Type, symbol: []const u8) Error!?Type {
    if (!ty.is_type_val)
        return null;

    if (!ty.isTaggedUnion())
        return null;

    const child = try ty.lookupSymbol(analyser, symbol) orelse
        return null;

    if (child.decl != .ast_node or !child.handle.document.tree.nodeTag(child.decl.ast_node).isContainerField())
        return null;

    return try analyser.resolveUnionTag(ty);
}

pub fn resolveFuncProtoOfCallable(analyser: *Analyser, ty: Type) error{OutOfMemory}!?Type {
    const deref_type = try analyser.resolveDerefType(ty) orelse ty;
    if (!deref_type.isFunc()) return null;
    return deref_type;
}

/// resolve a pointer dereference
/// `pointer.*`
pub fn resolveDerefType(analyser: *Analyser, pointer: Type) error{OutOfMemory}!?Type {
    const binding = try analyser.resolveDerefBinding(pointer) orelse return null;
    return binding.type;
}

pub fn resolveDerefBinding(analyser: *Analyser, pointer: Type) error{OutOfMemory}!?Binding {
    if (pointer.is_type_val) return null;

    switch (pointer.data) {
        .pointer => |info| switch (info.size) {
            .one, .c => return .{
                .type = try info.elem_ty.instanceTypeVal(analyser) orelse return null,
                .is_const = info.is_const,
            },
            .many, .slice => return null,
        },
        .ip_index => |payload| {
            const ty = payload.type;
            switch (analyser.ip.indexToKey(ty)) {
                .pointer_type => |pointer_info| switch (pointer_info.flags.size) {
                    .one, .c => return .{
                        .type = Type.fromIP(analyser, pointer_info.elem_type, null),
                        .is_const = pointer_info.flags.is_const,
                    },
                    .many, .slice => return null,
                },
                else => return null,
            }
        },
        else => return null,
    }
}

pub const BracketAccess = union(enum) {
    /// `lhs[index]`
    single: ?u64,
    /// `lhs[start.. :sentinel]`
    open: struct {
        start: ?u64,
        sentinel: InternPool.Index,
    },
    /// `lhs[start..end :sentinel]`
    range: struct {
        bounds: ?struct { u64, u64 },
        sentinel: InternPool.Index,
    },

    pub fn fromSlice(
        analyser: *Analyser,
        options: ResolveOptions,
        slice: Ast.full.Slice,
    ) Error!BracketAccess {
        const start_node = slice.ast.start;
        const end_node = slice.ast.end.unwrap() orelse
            return .{
                .open = .{
                    .start = try analyser.resolveIntegerLiteral(u64, options.at(start_node)),
                    .sentinel = try analyser.resolveOptionalIPValue(options, slice.ast.sentinel),
                },
            };

        const bounds = blk: {
            const start = try analyser.resolveIntegerLiteral(u64, options.at(start_node)) orelse
                break :blk null;

            const end = try analyser.resolveIntegerLiteral(u64, options.at(end_node)) orelse
                break :blk null;

            break :blk .{ start, end };
        };

        return .{
            .range = .{
                .bounds = bounds,
                .sentinel = try analyser.resolveOptionalIPValue(options, slice.ast.sentinel),
            },
        };
    }
};

/// Resolves slicing and array access
/// - `lhs[index]` (single)
/// - `lhs[start..]` (open)
/// - `lhs[start..end]` (range)
pub fn resolveBracketAccessType(analyser: *Analyser, lhs: Type, rhs: BracketAccess) error{OutOfMemory}!?Type {
    const binding = try analyser.resolveBracketAccess(.{ .type = lhs, .is_const = false }, rhs) orelse return null;
    return binding.type;
}

// TODO: copy indexing logic from Zig compiler to InternPool, and then delete bracketAccessTypeFromIPIndex
fn bracketAccessTypeFromIPIndex(analyser: *Analyser, ip_index: InternPool.Index) error{OutOfMemory}!Type {
    std.debug.assert(analyser.ip.typeOf(ip_index) == .type_type);
    return switch (analyser.ip.indexToKey(ip_index)) {
        .tuple_type => |info| {
            const types = try info.types.dupe(analyser.gpa, analyser.ip);
            defer analyser.gpa.free(types);

            const elem_ty_slice = try analyser.arena.alloc(Type, types.len);
            for (elem_ty_slice, types) |*elem_ty, ty|
                elem_ty.* = try analyser.bracketAccessTypeFromIPIndex(ty);

            return .{
                .data = .{ .tuple = elem_ty_slice },
                .is_type_val = true,
            };
        },
        .vector_type => |info| .{
            .data = .{
                .array = .{
                    .elem_count = info.len,
                    .sentinel = .none,
                    .elem_ty = try analyser.allocType(try analyser.bracketAccessTypeFromIPIndex(info.child)),
                },
            },
            .is_type_val = true,
        },
        .array_type => |info| .{
            .data = .{
                .array = .{
                    .elem_count = info.len,
                    .sentinel = info.sentinel,
                    .elem_ty = try analyser.allocType(try analyser.bracketAccessTypeFromIPIndex(info.child)),
                },
            },
            .is_type_val = true,
        },
        .pointer_type => |info| .{
            .data = .{
                .pointer = .{
                    .size = info.flags.size,
                    .sentinel = info.sentinel,
                    .is_const = info.flags.is_const,
                    .elem_ty = try analyser.allocType(try analyser.bracketAccessTypeFromIPIndex(info.elem_type)),
                },
            },
            .is_type_val = true,
        },
        else => Type.fromIP(analyser, .type_type, ip_index),
    };
}

pub fn resolveBracketAccess(analyser: *Analyser, lhs_binding: Binding, rhs: BracketAccess) error{OutOfMemory}!?Binding {
    const lhs = lhs_binding.type;
    if (lhs.is_type_val) return null;

    const is_const = switch (lhs.data) {
        .pointer => |info| info.is_const,
        else => lhs_binding.is_const,
    };

    var result: union(enum) { array: ?u64, slice: void } = .slice;
    var sentinel: InternPool.Index = .none;
    const elem_ty = elem: switch (lhs.data) {
        .tuple => |fields| switch (rhs) {
            .single => |index_maybe| {
                const index = index_maybe orelse return null;
                if (index >= fields.len) return null;
                const instance = try fields[@intCast(index)].instanceUnchecked(analyser);
                return .{ .type = instance, .is_const = is_const };
            },
            .open, .range => return null,
        },
        .array => |info| switch (rhs) {
            .single => {
                const instance = try info.elem_ty.instanceUnchecked(analyser);
                return .{ .type = instance, .is_const = is_const };
            },
            .open => |access| {
                if (access.start) |start| {
                    result = .{ .array = null };
                    if (info.elem_count) |elem_count| {
                        if (start <= elem_count) {
                            result = .{ .array = elem_count - start };
                        }
                    }
                }
                sentinel = access.sentinel;
                if (sentinel == .none) sentinel = info.sentinel;
                break :elem info.elem_ty;
            },
            .range => |access| {
                if (access.bounds) |bounds| {
                    result = .{ .array = null };
                    if (info.elem_count) |elem_count| {
                        const start, const end = bounds;
                        if (start <= end and start <= elem_count and end <= elem_count) {
                            result = .{ .array = end - start };
                        }
                    }
                }
                sentinel = access.sentinel;
                break :elem info.elem_ty;
            },
        },
        .pointer => |info| switch (info.size) {
            .one => switch (info.elem_ty.data) {
                .tuple, .array => continue :elem info.elem_ty.data,
                else => switch (rhs) {
                    .single, .open => return null,
                    .range => |access| {
                        if (access.sentinel != .none) return null;
                        const start, const end = access.bounds orelse return null;
                        if (start > end or start > 1 or end > 1) return null;
                        result = .{ .array = end - start };
                        break :elem info.elem_ty;
                    },
                },
            },
            .many, .slice, .c => switch (rhs) {
                .single => {
                    const instance = try info.elem_ty.instanceUnchecked(analyser);
                    return .{ .type = instance, .is_const = is_const };
                },
                .open => |access| {
                    sentinel = access.sentinel;
                    if (sentinel == info.sentinel) return lhs_binding;
                    if (sentinel == .none) sentinel = info.sentinel;
                    break :elem info.elem_ty;
                },
                .range => |access| {
                    if (access.bounds) |bounds| {
                        const start, const end = bounds;
                        result = .{ .array = if (start <= end) end - start else null };
                    }
                    sentinel = access.sentinel;
                    break :elem info.elem_ty;
                },
            },
        },
        .ip_index => |payload| {
            const ty = try analyser.bracketAccessTypeFromIPIndex(payload.type);
            const instance = try ty.instanceUnchecked(analyser);
            const binding: Binding = .{ .type = instance, .is_const = is_const };
            if (lhs.eql(binding.type)) return null;
            return analyser.resolveBracketAccess(binding, rhs);
        },
        else => return null,
    };

    switch (result) {
        .array => |elem_count| {
            const array_ty = try Type.createArrayType(analyser, elem_count, sentinel, elem_ty.*);
            const pointer_ty = try Type.createPointerType(analyser, .one, .none, is_const, array_ty);
            const pointer_instance = try pointer_ty.instanceUnchecked(analyser);
            return .{ .type = pointer_instance, .is_const = true };
        },
        .slice => {
            const slice_ty = try Type.createPointerType(analyser, .slice, sentinel, is_const, elem_ty.*);
            const slice_instance = try slice_ty.instanceUnchecked(analyser);
            return .{ .type = slice_instance, .is_const = true };
        },
    }
}

pub fn resolvePropertyType(analyser: *Analyser, ty: Type, name: []const u8) error{OutOfMemory}!?Type {
    if (ty.is_type_val)
        return null;

    switch (ty.data) {
        .pointer => |info| switch (info.size) {
            .one => {
                if (std.mem.eql(u8, "*", name)) {
                    return info.elem_ty.instanceTypeVal(analyser);
                }
                // One level of indirection is handled by resolveDerefType
            },
            .slice => {
                if (std.mem.eql(u8, "len", name)) {
                    return Type.fromIP(analyser, .usize_type, null);
                }

                if (std.mem.eql(u8, "ptr", name)) {
                    return .{
                        .data = .{
                            .pointer = .{
                                .size = .many,
                                .sentinel = info.sentinel,
                                .is_const = info.is_const,
                                .elem_ty = info.elem_ty,
                            },
                        },
                        .is_type_val = false,
                    };
                }
            },
            .many, .c => {},
        },

        .array => |info| {
            if (std.mem.eql(u8, "len", name)) {
                if (info.elem_count) |elem_count| {
                    const index = try analyser.ip.get(
                        .{ .int_u64_value = .{ .ty = .usize_type, .int = elem_count } },
                    );
                    return Type.fromIP(analyser, .usize_type, index);
                }
                return Type.fromIP(analyser, .usize_type, null);
            }
        },

        .tuple => |info| {
            if (std.mem.eql(u8, "len", name)) {
                const index = try analyser.ip.get(
                    .{ .int_u64_value = .{ .ty = .usize_type, .int = info.len } },
                );
                return Type.fromIP(analyser, .usize_type, index);
            }
            if (!allDigits(name)) return null;
            const index = std.fmt.parseInt(u16, name, 10) catch return null;
            return try analyser.resolveBracketAccessType(ty, .{ .single = index });
        },

        .optional => |child_ty| {
            if (std.mem.eql(u8, "?", name)) {
                return child_ty.instanceTypeVal(analyser);
            }
        },

        .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
            .pointer_type => |pointer_info| switch (pointer_info.flags.size) {
                .one => {
                    if (std.mem.eql(u8, "*", name)) {
                        return Type.fromIP(analyser, pointer_info.elem_type, null);
                    }
                },
                .slice => {
                    if (std.mem.eql(u8, "len", name)) {
                        return Type.fromIP(analyser, .usize_type, null);
                    }

                    if (std.mem.eql(u8, "ptr", name)) {
                        var slice_ptr_info = pointer_info;
                        slice_ptr_info.flags.size = .many;
                        const slice_ptr_ty = try analyser.ip.get(.{ .pointer_type = slice_ptr_info });
                        return Type.fromIP(analyser, slice_ptr_ty, null);
                    }
                },
                .many, .c => {},
            },

            .array_type => |array_info| {
                if (std.mem.eql(u8, "len", name)) {
                    const index = try analyser.ip.get(.{
                        .int_u64_value = .{
                            .ty = .usize_type,
                            .int = array_info.len,
                        },
                    });
                    return Type.fromIP(analyser, .usize_type, index);
                }
            },

            .tuple_type => |tuple_info| {
                if (std.mem.eql(u8, "len", name)) {
                    const index = try analyser.ip.get(.{
                        .int_u64_value = .{
                            .ty = .usize_type,
                            .int = tuple_info.types.len,
                        },
                    });
                    return Type.fromIP(analyser, .usize_type, index);
                }
                if (!allDigits(name)) return null;
                const index = std.fmt.parseInt(u16, name, 10) catch return null;
                return try analyser.resolveBracketAccessType(ty, .{ .single = index });
            },

            .optional_type => |optional_info| {
                if (std.mem.eql(u8, "?", name)) {
                    return Type.fromIP(analyser, optional_info.payload_type, null);
                }
            },

            else => {},
        },

        else => {},
    }

    return null;
}

fn allDigits(str: []const u8) bool {
    for (str) |c| {
        if (!std.ascii.isDigit(c)) return false;
    }
    return true;
}

fn resolveArrayMult(analyser: *Analyser, ty: Type, mult: ?u64) Error!?Type {
    if (ty.is_type_val) return null;
    const array_info = ty.arrayInfo(analyser) orelse return null;
    const old_count, const sentinel, const elem_ty = array_info;
    const new_count = blk: {
        const c = old_count orelse break :blk null;
        const m = mult orelse break :blk null;
        break :blk std.math.mul(u64, c, m) catch null;
    };
    const array_ty = try Type.createArrayType(analyser, new_count, sentinel, elem_ty);
    return try array_ty.instanceUnchecked(analyser);
}

fn resolveArrayCat(analyser: *Analyser, l_ty: Type, r_ty: Type) Error!?Type {
    if (l_ty.is_type_val) return null;
    if (r_ty.is_type_val) return null;
    const l_info = l_ty.arrayInfo(analyser) orelse return null;
    const r_info = r_ty.arrayInfo(analyser) orelse return null;
    const l_count, const l_sentinel, const l_elem_ty = l_info;
    const r_count, const r_sentinel, const r_elem_ty = r_info;
    _ = r_elem_ty; // TODO: Do peer type resolution
    const elem_count = blk: {
        const l = l_count orelse break :blk null;
        const r = r_count orelse break :blk null;
        break :blk std.math.add(u64, l, r) catch null;
    };
    const sentinel = blk: {
        if (l_sentinel == .unknown_unknown) break :blk .unknown_unknown;
        if (r_sentinel == .unknown_unknown) break :blk .unknown_unknown;
        if (l_sentinel == .none) break :blk r_sentinel;
        if (r_sentinel == .none) break :blk l_sentinel;
        if (l_sentinel == r_sentinel) break :blk l_sentinel;
        break :blk .none;
    };
    const array_ty = try Type.createArrayType(analyser, elem_count, sentinel, l_elem_ty);
    return try array_ty.instanceUnchecked(analyser);
}

/// A sentinel is written in the body that spells the slice, and it is
/// frequently a `comptime` formal of the enclosing generic — `[:0]T`
/// inside one declaration names that declaration's parameter.  So this
/// reads it in the caller's own frame rather than against the file alone.
fn resolveOptionalIPValue(
    analyser: *Analyser,
    options: ResolveOptions,
    optional_node: Ast.Node.OptionalIndex,
) Error!InternPool.Index {
    const node = optional_node.unwrap() orelse return .none;
    return try analyser.resolveInternPoolValue(options.at(node)) orelse .unknown_unknown;
}

fn resolveCoercedIPValue(
    analyser: *Analyser,
    ip_ty: InternPool.Index,
    options: ResolveOptions,
) Error!?InternPool.Index {
    if (!analyser.ip.isType(ip_ty)) return null;
    const ty = try analyser.resolveTypeOfNode(options) orelse return null;
    const ip_index = ty.ipIndex() orelse return null;
    if (analyser.ip.isUndefined(ip_index)) return null;

    var arena_allocator: std.heap.ArenaAllocator = .init(analyser.gpa);
    defer arena_allocator.deinit();
    const arena = arena_allocator.allocator();

    var err_msg: ErrorMsg = undefined;
    const new_index = try analyser.ip.coerce(arena, ip_ty, ip_index, builtin.target, &err_msg);

    if (new_index == .none) return null;
    if (analyser.ip.isUnknown(new_index)) return null;
    return new_index;
}

fn resolveInternPoolValue(analyser: *Analyser, options: ResolveOptions) Error!?InternPool.Index {
    const resolved_length = try analyser.resolveTypeOfNode(options) orelse return null;
    switch (resolved_length.data) {
        .ip_index => |payload| return payload.index,
        else => return null,
    }
}

pub fn resolveIntegerLiteral(analyser: *Analyser, comptime T: type, options: ResolveOptions) Error!?T {
    const ip_index = try analyser.resolveInternPoolValue(options) orelse return null;
    return analyser.ip.toInt(ip_index, T);
}

/// Whether `index` is an interned integer CONSTANT.  Only those are read
/// as values: every other kind of value — a pointer, a struct,
/// `undefined`, `null` — stays unknown, which is what keeps an
/// unevaluated factory from exporting a number.
fn isInternedIntValue(ip: *InternPool, index: InternPool.Index) bool {
    return switch (ip.indexToKey(index)) {
        .int_u64_value, .int_i64_value, .int_big_value => true,
        else => false,
    };
}

/// The integer value `ty` carries, when it carries one.
fn internedIntValueOf(analyser: *Analyser, ty: Type) ?InternPool.Index {
    const index = ty.ipIndex() orelse return null;
    if (!isInternedIntValue(analyser.ip, index)) return null;
    return index;
}

/// The type `ty` DENOTES, independently of any value it carries.
///
/// A parameter's stored type is the TYPE-VALUED form:
/// `Type.fromIP(.type_type, .comptime_int_type)` for
/// `digest_bits: comptime_int`, where `ip_index.index` is the type named
/// and `ip_index.type` is the metatype `type`.  Reading `ip_index.type`
/// there answers `type` for every parameter, so nothing would ever bind
/// and no coercion would have a declared type to aim at.  An ordinary
/// VALUE operand is the other way round, and keeps `ip_index.type`.
fn declaredTypeOf(ty: Type) ?InternPool.Index {
    return switch (ty.data) {
        .ip_index => |payload| if (ty.is_type_val) payload.index else payload.type,
        else => null,
    };
}

/// The integer operations a resolved expression is evaluated for.  Each
/// is exact on `i128`; an overflowing one is refused rather than wrapped,
/// because the engine would otherwise answer a number Zig cannot produce.
const ComptimeIntOp = enum {
    add,
    sub,
    mul,
    div,
    mod,
    bit_and,
    bit_or,
    bit_xor,
};

fn comptimeIntOpOf(tag: Ast.Node.Tag) ?ComptimeIntOp {
    return switch (tag) {
        .add => .add,
        .sub => .sub,
        .mul => .mul,
        .div => .div,
        .mod => .mod,
        .bit_and => .bit_and,
        .bit_or => .bit_or,
        .bit_xor => .bit_xor,
        else => null,
    };
}

/// `lhs op rhs` as an interned integer value, when both operands are
/// integer constants the operation is exact on, and the result is
/// representable in `result_type`.  Null otherwise, and null means the
/// caller keeps the value-less answer it already had.
fn comptimeIntValue(
    analyser: *Analyser,
    op: ComptimeIntOp,
    lhs: InternPool.Index,
    rhs: InternPool.Index,
    result_type: InternPool.Index,
) Error!?InternPool.Index {
    const a = analyser.ip.toInt(lhs, i128) orelse return null;
    const b = analyser.ip.toInt(rhs, i128) orelse return null;
    const value: i128 = switch (op) {
        .add => std.math.add(i128, a, b) catch return null,
        .sub => std.math.sub(i128, a, b) catch return null,
        .mul => std.math.mul(i128, a, b) catch return null,
        .div => if (b == 0) return null else std.math.divTrunc(i128, a, b) catch return null,
        .mod => if (b == 0) return null else std.math.rem(i128, a, b) catch return null,
        .bit_and => a & b,
        .bit_or => a | b,
        .bit_xor => a ^ b,
    };

    const natural: InternPool.Index = if (std.math.cast(u64, value)) |unsigned|
        try analyser.ip.get(.{ .int_u64_value = .{ .ty = .comptime_int_type, .int = unsigned } })
    else if (std.math.cast(i64, value)) |signed|
        try analyser.ip.get(.{ .int_i64_value = .{ .ty = .comptime_int_type, .int = signed } })
    else big: {
        var big = try std.math.big.int.Managed.init(analyser.gpa);
        defer big.deinit();
        try big.set(value);
        break :big try analyser.ip.getBigInt(.comptime_int_type, big.toConst());
    };

    var err_msg: ErrorMsg = undefined;
    const coerced = try analyser.ip.coerce(analyser.arena, result_type, natural, builtin.target, &err_msg);
    if (coerced == .none) return null;
    if (analyser.ip.isUnknown(coerced)) return null;
    return coerced;
}

/// `peer` carrying the value of `lhs op rhs` when both operands are
/// integer constants and the peer type is an integer type that can
/// represent the result.  `peer` is returned unchanged in every other
/// case, so no expression that was unknown before becomes known here
/// without both of its operands actually being known.
fn withComptimeIntValue(
    analyser: *Analyser,
    op: ComptimeIntOp,
    peer: Type,
    lhs: Type,
    rhs: Type,
) Error!Type {
    const result_type = declaredTypeOf(peer) orelse return peer;
    switch (analyser.ip.zigTypeTag(result_type) orelse return peer) {
        .int, .comptime_int => {},
        else => return peer,
    }
    const lhs_value = internedIntValueOf(analyser, lhs) orelse return peer;
    const rhs_value = internedIntValueOf(analyser, rhs) orelse return peer;
    const value = (try comptimeIntValue(analyser, op, lhs_value, rhs_value, result_type)) orelse return peer;
    if (!isInternedIntValue(analyser.ip, value)) return peer;
    return Type.fromIP(analyser, analyser.ip.typeOf(value), value);
}

const primitives: std.StaticStringMap(InternPool.Index) = .initComptime(.{
    .{ "anyerror", .anyerror_type },
    .{ "anyframe", .anyframe_type },
    .{ "anyopaque", .anyopaque_type },
    .{ "bool", .bool_type },
    .{ "c_int", .c_int_type },
    .{ "c_long", .c_long_type },
    .{ "c_longdouble", .c_longdouble_type },
    .{ "c_longlong", .c_longlong_type },
    .{ "c_char", .c_char_type },
    .{ "c_short", .c_short_type },
    .{ "c_uint", .c_uint_type },
    .{ "c_ulong", .c_ulong_type },
    .{ "c_ulonglong", .c_ulonglong_type },
    .{ "c_ushort", .c_ushort_type },
    .{ "comptime_float", .comptime_float_type },
    .{ "comptime_int", .comptime_int_type },
    .{ "f128", .f128_type },
    .{ "f16", .f16_type },
    .{ "f32", .f32_type },
    .{ "f64", .f64_type },
    .{ "f80", .f80_type },
    .{ "false", .bool_false },
    .{ "i16", .i16_type },
    .{ "i32", .i32_type },
    .{ "i64", .i64_type },
    .{ "i128", .i128_type },
    .{ "i8", .i8_type },
    .{ "isize", .isize_type },
    .{ "noreturn", .noreturn_type },
    .{ "null", .null_value },
    .{ "true", .bool_true },
    .{ "type", .type_type },
    .{ "u16", .u16_type },
    .{ "u29", .u29_type },
    .{ "u32", .u32_type },
    .{ "u64", .u64_type },
    .{ "u128", .u128_type },
    .{ "u1", .u1_type },
    .{ "u8", .u8_type },
    .{ "undefined", .undefined_value },
    .{ "usize", .usize_type },
    .{ "void", .void_type },
});

pub fn resolvePrimitive(analyser: *Analyser, identifier_name: []const u8) error{OutOfMemory}!?InternPool.Index {
    if (primitives.get(identifier_name)) |primitive| return primitive;

    if (identifier_name.len < 2) return null;
    const signedness: std.builtin.Signedness = switch (identifier_name[0]) {
        'i' => .signed,
        'u' => .unsigned,
        else => return null,
    };
    for (identifier_name[1..]) |c| {
        switch (c) {
            '0'...'9' => {},
            else => return null,
        }
    }

    const bits = std.fmt.parseUnsigned(u16, identifier_name[1..], 10) catch return null;

    return try analyser.ip.get(.{ .int_type = .{
        .bits = bits,
        .signedness = signedness,
    } });
}

pub fn resolveStringLiteral(analyser: *Analyser, options: ResolveOptions) Error!?[]const u8 {
    var node_with_handle = options.node_handle;
    if (try analyser.resolveVarDeclAlias(.{
        .decl = .{ .ast_node = options.node_handle.node },
        .handle = options.node_handle.handle,
        .container_type = options.container_type,
    })) |decl_with_handle| {
        if (decl_with_handle.decl == .ast_node) {
            node_with_handle = .{
                .node = decl_with_handle.decl.ast_node,
                .handle = decl_with_handle.handle,
            };
        }
    }
    const tree = &node_with_handle.handle.document.tree;
    switch (tree.nodeTag(node_with_handle.node)) {
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, node_with_handle.node) orelse return null;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node_with_handle.node)), "@tagName")) {
                // `@field(value, "name")` evaluates to the SELECTED FIELD'S
                // VALUE, not to a name.  Answering it by echoing the name
                // argument would report `"key"` for an `Entry.key: u32`,
                // which is a fabrication, so this refuses.
                return null;
            }
            if (params.len != 1) return null;
            return try resolveBoundTagName(analyser, options, params[0]);
        },
        else => {},
    }
    // A formal bound to a string literal carries its bytes, so reading that
    // formal by name answers them.  The store is keyed by the formal's
    // DECLARATION token, while this identifier carries the USE token — the
    // two are different tokens — so the name is resolved to its declaration
    // first and the binding is read under that key.
    if (options.container_type) |container| {
        if (container.data == .container and tree.nodeTag(node_with_handle.node) == .identifier) {
            const name = offsets.identifierTokenToNameSlice(tree, ast.identifierTokenFromIdentifierNode(tree, node_with_handle.node) orelse return null);
            const decl = (try container.lookupSymbol(analyser, name)) orelse
                (try analyser.lookupSymbolGlobal(node_with_handle.handle, name, tree.tokenStart(tree.nodeMainToken(node_with_handle.node))));
            if (decl) |found| {
                const bound = container.data.container.bound_values.get(.{
                    .token = found.nameToken(),
                    .handle = found.handle,
                });
                if (bound) |value| switch (value) {
                    .string => |bytes| return bytes,
                    .enum_tag => {},
                };
            }
        }
    }

    const string_literal_node = switch (node_with_handle.handle.document.tree.nodeTag(node_with_handle.node)) {
        .string_literal => node_with_handle.node,
        .global_var_decl,
        .local_var_decl,
        .aligned_var_decl,
        .simple_var_decl,
        => blk: {
            const var_decl = node_with_handle.handle.document.tree.fullVarDecl(node_with_handle.node).?;
            const init_node = var_decl.ast.init_node.unwrap() orelse return null;
            if (node_with_handle.handle.document.tree.nodeTag(init_node) != .string_literal) return null;
            break :blk init_node;
        },
        else => return null,
    };
    const field_name_token = node_with_handle.handle.document.tree.nodeMainToken(string_literal_node);
    const field_name = offsets.tokenToSlice(&node_with_handle.handle.document.tree, field_name_token);

    // Need at least one char between the quotes, eg "a"
    if (field_name.len < 2) return null;
    const raw = field_name[1 .. field_name.len - 1];

    // A literal with no escape sequence IS its own contents, so it borrows
    // the source text and allocates nothing.  Anything with a backslash is
    // decoded by the canonical routine the language itself uses — this
    // engine owns no second parser, and inventing escape rules here would
    // be a second answer to the same question.
    if (std.mem.indexOfScalar(u8, raw, '\\') == null) return raw;
    return std.zig.string_literal.parseAlloc(analyser.arena, raw) catch |err| switch (err) {
        // A literal this parser rejects is a literal with no value, not an
        // excuse to hand back the raw text: the raw text is not the string.
        error.InvalidLiteral => return null,
        // OutOfMemory is already part of `Error`; it propagates unchanged.
        error.OutOfMemory => return error.OutOfMemory,
    };
}
/// The NAME of the enum tag `node` names, when the frame this read happens
/// in actually bound that formal to one.
///
/// A tag that was never bound — a runtime value, or a formal read outside
/// the call that supplied it — has no name this engine can know.  Naming
/// one from the formal's spelling or from the enum's member list would be a
/// fabrication, so that reads as unknown.
fn resolveBoundTagName(analyser: *Analyser, options: ResolveOptions, node: Ast.Node.Index) Error!?[]const u8 {
    const container = options.container_type orelse return null;
    const info = switch (container.data) {
        .container => |info| info,
        else => return null,
    };
    const handle = options.node_handle.handle;
    const tree = &handle.document.tree;
    if (tree.nodeTag(node) != .identifier) return null;
    const name_token = ast.identifierTokenFromIdentifierNode(tree, node) orelse return null;
    const name = offsets.identifierTokenToNameSlice(tree, name_token);
    // Same declaration-key rule as the string reader: the store is keyed by
    // the formal's declaration token, not by this use.
    const decl = (try container.lookupSymbol(analyser, name)) orelse
        (try analyser.lookupSymbolGlobal(handle, name, tree.tokenStart(name_token))) orelse return null;
    const bound = info.bound_values.get(.{ .token = decl.nameToken(), .handle = decl.handle }) orelse return null;
    return switch (bound) {
        .enum_tag => |tag| tag.name,
        .string => null,
    };
}

fn resolveErrorSetIPIndex(analyser: *Analyser, options: ResolveOptions) Error!?InternPool.Index {
    const ty = try analyser.resolveTypeOfNodeInternal(options) orelse return null;
    if (!ty.is_type_val) return null;
    const ip_index = switch (ty.data) {
        .ip_index => |payload| payload.index orelse return null,
        else => return null,
    };
    if (analyser.ip.zigTypeTag(ip_index) != .error_set) return null;
    return ip_index;
}

fn coerceIP(analyser: *Analyser, dest_ty: InternPool.Index, inst: InternPool.Index) error{OutOfMemory}!?InternPool.Index {
    if (inst == .none)
        return .none;
    var err_msg: ErrorMsg = undefined;
    const coerced_sentinel = try analyser.ip.coerce(analyser.arena, dest_ty, inst, builtin.target, &err_msg);
    if (coerced_sentinel != .none)
        return coerced_sentinel;
    return null;
}

fn resolvePeerTypes(analyser: *Analyser, a: Type, b: Type) error{OutOfMemory}!?Type {
    if (a.is_type_val or b.is_type_val) return null;
    if (a.eql(b)) return a;

    if (a.data == .ip_index and b.data == .ip_index) {
        const a_type = a.data.ip_index.type;
        const b_type = b.data.ip_index.type;
        if (try analyser.resolvePeerTypesIP(a_type, b_type)) |resolved_type| {
            return Type.fromIP(analyser, resolved_type, null);
        }
    }

    return try analyser.resolvePeerTypesInternal(a, b) orelse try analyser.resolvePeerTypesInternal(b, a);
}

fn resolvePeerTypesIP(analyser: *Analyser, a: InternPool.Index, b: InternPool.Index) error{OutOfMemory}!?InternPool.Index {
    const resolved = try analyser.ip.resolvePeerTypes(&.{ a, b }, builtin.target);
    if (resolved == .none) return null;
    return resolved;
}

fn resolvePeerErrorSets(analyser: *Analyser, a: Type, b: Type) error{OutOfMemory}!?Type {
    if (a.data != .ip_index) return null;
    if (b.data != .ip_index) return null;
    if (a.data.ip_index.type != .type_type) return null;
    if (b.data.ip_index.type != .type_type) return null;
    const a_index = a.data.ip_index.index orelse return null;
    const b_index = b.data.ip_index.index orelse return null;
    if (analyser.ip.zigTypeTag(a_index) != .error_set) return null;
    if (analyser.ip.zigTypeTag(b_index) != .error_set) return null;
    const resolved_index = try analyser.ip.errorSetMerge(a_index, b_index);
    return Type.fromIP(analyser, .type_type, resolved_index);
}

fn resolvePeerTypesInternal(analyser: *Analyser, a: Type, b: Type) error{OutOfMemory}!?Type {
    switch (a.data) {
        .compile_error => return b,
        .optional => |a_type| {
            if (a_type.eql(try b.typeOf(analyser))) {
                return a;
            }
            switch (b.data) {
                .error_union => |b_info| {
                    if (a_type.eql(b_info.payload.*)) {
                        return .{
                            .data = .{
                                .error_union = .{
                                    .error_set = b_info.error_set,
                                    .payload = try analyser.allocType(try a.typeOf(analyser)),
                                },
                            },
                            .is_type_val = false,
                        };
                    }
                },
                else => {},
            }
        },
        .error_union => |a_info| {
            if (a_info.payload.eql(try b.typeOf(analyser))) {
                return a;
            }
            switch (b.data) {
                .error_union => |b_info| {
                    const resolved_error_set = blk: {
                        const a_error_set = a_info.error_set orelse break :blk null;
                        const b_error_set = b_info.error_set orelse break :blk null;
                        if (a_error_set.eql(b_error_set.*)) break :blk a_error_set;
                        const resolved_error_set = try analyser.resolvePeerErrorSets(a_error_set.*, b_error_set.*) orelse break :blk null;
                        break :blk try analyser.allocType(resolved_error_set);
                    };
                    const resolved_payload = blk: {
                        if (a_info.payload.eql(b_info.payload.*)) break :blk a_info.payload;
                        const a_instance = try a_info.payload.instanceTypeVal(analyser) orelse return null;
                        const b_instance = try b_info.payload.instanceTypeVal(analyser) orelse return null;
                        const resolved_instance = try analyser.resolvePeerTypes(a_instance, b_instance) orelse return null;
                        break :blk try analyser.allocType(try resolved_instance.typeOf(analyser));
                    };
                    return .{
                        .data = .{
                            .error_union = .{
                                .error_set = resolved_error_set,
                                .payload = resolved_payload,
                            },
                        },
                        .is_type_val = false,
                    };
                },
                else => {},
            }
        },
        .ip_index => |a_payload| switch (analyser.ip.zigTypeTag(a_payload.type) orelse return null) {
            .noreturn => return b,
            .null => switch (b.data) {
                .optional => return b,
                .error_union => |b_info| {
                    return .{
                        .data = .{
                            .error_union = .{
                                .error_set = b_info.error_set,
                                .payload = try analyser.allocType(.{
                                    .data = .{ .optional = try analyser.allocType(b_info.payload.*) },
                                    .is_type_val = true,
                                }),
                            },
                        },
                        .is_type_val = false,
                    };
                },
                else => return .{
                    .data = .{ .optional = try analyser.allocType(try b.typeOf(analyser)) },
                    .is_type_val = false,
                },
            },
            .error_set => switch (b.data) {
                .error_union => |b_info| {
                    const resolved_error_set = blk: {
                        const a_error_set = try a.typeOf(analyser);
                        const b_error_set = b_info.error_set orelse break :blk null;
                        if (a_error_set.eql(b_error_set.*)) break :blk b_error_set;
                        const resolved_error_set = try analyser.resolvePeerErrorSets(a_error_set, b_error_set.*) orelse break :blk null;
                        break :blk try analyser.allocType(resolved_error_set);
                    };
                    return .{
                        .data = .{
                            .error_union = .{
                                .error_set = resolved_error_set,
                                .payload = b_info.payload,
                            },
                        },
                        .is_type_val = false,
                    };
                },
                else => return .{
                    .data = .{
                        .error_union = .{
                            .error_set = try analyser.allocType(try a.typeOf(analyser)),
                            .payload = try analyser.allocType(try b.typeOf(analyser)), // zbc-disable-line: struct-literal-multiple-try — allocType uses analyser.arena; error path frees the arena
                        },
                    },
                    .is_type_val = false,
                },
            },
            else => {},
        },
        else => {},
    }

    return null;
}

/// Is the call site at `source_index` written inside THIS container — so
/// that this container is that call site's enclosing frame?
///
/// Document and module are not enough.  Two generic containers in one
/// file are two different frames, and reading one container's call site
/// under the other is exactly how `@This()` and a member name end up
/// naming the wrong container — including a file-root container
/// "reaching" a call site that really belongs to a nested type.
///
/// The question that settles it is the one `innermostContainer` already
/// answers: the NEAREST enclosing container at the call site must BE this
/// container.  When it is not — another container, a nested one, another
/// file, another module — this container is not that call site's frame and
/// the conservative union over every call site is the only sound answer.
fn containerReachesCallSite(
    analyser: *Analyser,
    container: Type,
    ref_handle: DocumentStore.Handle,
    source_index: usize,
) Error!bool {
    const scope_handle = switch (container.data) {
        .container => |info| info.scope_handle,
        else => return false,
    };
    if (scope_handle.handle.module != ref_handle.module) return false;
    if (!scope_handle.handle.document.uri.eql(ref_handle.document.uri)) return false;

    const nearest = try analyser.innermostContainer(ref_handle, source_index);
    const nearest_scope = switch (nearest.data) {
        .container => |info| info.scope_handle,
        else => return false,
    };
    if (nearest_scope.handle.module != scope_handle.handle.module) return false;
    if (!nearest_scope.handle.document.uri.eql(scope_handle.handle.document.uri)) return false;
    return nearest_scope.scope == scope_handle.scope;
}

fn resolveCallsiteReferences(analyser: *Analyser, decl_handle: DeclWithHandle) Error!?Type {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const pay = switch (decl_handle.decl) {
        .function_parameter => |pay| pay,
        else => return null,
    };

    const tree = &decl_handle.handle.document.tree;

    if (!analyser.collect_callsite_references) return null;

    const key: CallsiteKey = .{
        .param = pay,
        .handle = decl_handle.handle,
        .container_type = decl_handle.container_type,
    };

    if (analyser.resolved_callsites.get(key)) |settled| return settled;

    // Protection against recursive callsite resolution.  A STACK, not a
    // null marker in the answer map: a call site reached while this
    // parameter's own call sites are still being collected belongs to
    // whatever frame that call site is in, not to this walk — answering it
    // with this walk's unfinished state would report "unknown" for work
    // that is merely in progress.  The comparison is the whole key, so a
    // walk under one actual container never blocks the same formal under
    // another.
    for (analyser.resolving_callsites.items) |in_progress| {
        if (CallsiteKey.Context.eql(.{}, in_progress, key)) return null;
    }
    try analyser.resolving_callsites.append(analyser.gpa, key);
    defer _ = analyser.resolving_callsites.pop();

    const func_decl: Declaration = .{ .ast_node = pay.func };

    var func_buf: [1]Ast.Node.Index = undefined;
    const func = tree.fullFnProto(&func_buf, pay.func).?;

    var func_params_len: usize = 0;

    var it: ast.FnParamIterator = .init(&func, tree);
    while (it.next()) |_| {
        func_params_len += 1;
    }

    const refs = try callsiteReferences(
        analyser,
        .{ .decl = func_decl, .handle = decl_handle.handle, .container_type = decl_handle.container_type },
    );

    var possible: std.ArrayList(Type.TypeWithDescriptor) = .empty;

    for (refs.items) |ref| {
        // The call site may live in a different document than the
        // declaration; its node index means nothing in `tree`.
        const ref_tree = &ref.handle.document.tree;
        var call_buf: [1]Ast.Node.Index = undefined;
        const call = ref_tree.fullCall(&call_buf, ref.node).?;

        const real_param_idx = if (func_params_len != 0 and pay.param_index != 0 and call.ast.params.len == func_params_len - 1)
            pay.param_index - 1
        else
            pay.param_index;

        if (real_param_idx >= call.ast.params.len) continue;

        var ty = resolve_ty: {
            // don't resolve callsite references while resolving callsite references
            const old_collect_callsite_references = analyser.collect_callsite_references;
            defer analyser.collect_callsite_references = old_collect_callsite_references;
            analyser.collect_callsite_references = false;

            // The argument is written in the CALLER's body, so it is read
            // in the caller's frame — and only when this container IS that
            // frame.  A same-file call site inside a different container,
            // or inside a nested one, is not reached by it: reading it
            // here would name the wrong `@This()` and the wrong member,
            // and the conservative union is the only sound answer left.
            const ref_source_index = ref_tree.tokenStart(ref_tree.nodeMainToken(ref.node));
            const arg_options: ResolveOptions = .{
                .node_handle = .of(call.ast.params[real_param_idx], ref.handle),
                .container_type = if (decl_handle.container_type) |container|
                    if (try containerReachesCallSite(analyser, container, ref.handle, ref_source_index)) container else null
                else
                    null,
            };

            break :resolve_ty try analyser.resolveTypeOfNode(arg_options) orelse continue;
        };

        ty = try ty.typeOf(analyser);
        std.debug.assert(ty.is_type_val);

        const loc = offsets.tokenToPosition(ref_tree, ref_tree.nodeMainToken(call.ast.params[real_param_idx]), .@"utf-8");
        try possible.append(analyser.arena, .{
            .type = ty,
            .descriptor = try std.fmt.allocPrint(analyser.arena, "{s}:{d}:{d}", .{ ref.handle.document.uri.raw, loc.line + 1, loc.character + 1 }),
        });
    }

    const maybe_type = try Type.fromEither(analyser, possible.items);
    if (maybe_type) |ty| try analyser.resolved_callsites.put(analyser.gpa, key, ty);
    return maybe_type;
}

/// The single prong a `switch` provably takes, when the selector is an
/// integer constant and exactly one prong's value list names it.
///
/// `options` is the enclosing frame, and it is what makes this work on a
/// generic: a selector or a prong value written as a reflection over the
/// switch's OWN parameter — `std.hash` switching on `@typeInfo(K)`,
/// `std.meta` on `@Enum` — carries those bindings only when it is read
/// with them, and without them both sides stay unknown and every valid
/// narrowing goes unanswered.  An ordinary file-scope switch passes
/// `ResolveOptions.of`, which is exactly what this did before and still
/// answers the same.
///
/// Everything else answers null and keeps the conservative Either the
/// caller would have built: a selector the engine cannot read, a case
/// value it cannot read, a range (whose span is not compared here), an
/// `else` prong, a `break` that can supply the result, and a switch
/// where two prongs claim the same value.  Narrowing on any of those
/// would be a guess about which arm ran.
fn narrowSwitchToMatchingProng(
    analyser: *Analyser,
    options: ResolveOptions,
    switch_node: Ast.full.Switch,
) Error!?Type {
    const handle = options.node_handle.handle;
    const tree = &handle.document.tree;
    // A labelled switch can `break` a value into the result from any
    // arm, so which arm supplies it is not this question's to answer.
    if (switch_node.label_token != null) return null;

    const selector = try analyser.resolveTypeOfNodeInternal(options.at(switch_node.ast.condition)) orelse return null;
    const selector_value = internedIntValueOf(analyser, selector) orelse return null;
    const wanted = analyser.ip.toInt(selector_value, i128) orelse return null;

    var matched: ?Type = null;
    for (switch_node.ast.cases) |case| {
        const switch_case = tree.fullSwitchCase(case).?;
        // No values means `else`; which prong that is depends on every
        // other value list, so it never narrows on its own.
        if (switch_case.ast.values.len == 0) continue;

        var prong_matches = false;
        for (switch_case.ast.values) |case_value| {
            const case_ty = try analyser.resolveTypeOfNodeInternal(options.at(case_value)) orelse {
                prong_matches = false;
                break;
            };
            const case_value_index = internedIntValueOf(analyser, case_ty) orelse {
                prong_matches = false;
                break;
            };
            const actual = analyser.ip.toInt(case_value_index, i128) orelse {
                prong_matches = false;
                break;
            };
            if (actual == wanted) prong_matches = true;
        }
        if (!prong_matches) continue;
        if (matched != null) return null;
        matched = try analyser.resolveTypeOfNodeInternal(options.at(switch_case.ast.target_expr));
    }
    return matched;
}

/// Whether `param` can be READ at comptime, and so has an actual value
/// this call site can supply: one declared `comptime`, or one declared
/// `comptime_int`, which has no runtime representation at all — that is
/// how `std` writes `digest_bits: comptime_int` without the keyword.
///
/// Only an INTEGER type qualifies.  `type` is not one, so a
/// `comptime T: type` argument can never be mistaken for the
/// parameter's own value, and a struct, pointer or slice parameter binds
/// nothing either.
fn isComptimeReadableParameter(analyser: *Analyser, param: Type.Data.Parameter) bool {
    const declared = declaredTypeOf(param.type) orelse return false;
    switch (analyser.ip.zigTypeTag(declared) orelse return false) {
        .int, .comptime_int, .bool => {},
        else => return false,
    }
    if (param.modifier) |modifier| {
        if (modifier == .comptime_param) return true;
    }
    return declared == .comptime_int_type;
}

/// Is this parameter declared `comptime` at all?
///
/// A WIDER question than `isComptimeReadableParameter`, which asks whether
/// a value can be READ for this parameter — today only an integer, since an
/// enum tag and a string literal have no value representation to read.
/// This one asks only whether the parameter is a comptime formal, so that
/// it REACHES the binding machinery instead of being skipped whole.
///
/// It never causes a binding: nothing is invented from a declaration name,
/// and a formal with no readable value still binds nothing and is still
/// answered conservatively.
fn isComptimeFormal(param: Type.Data.Parameter) bool {
    if (param.modifier) |modifier| {
        if (modifier == .comptime_param) return true;
    }
    return false;
}

/// The ACTUAL value of `arg` as a `BoundValue`, when `arg` is written as
/// an enum tag or a string literal and `declared` says that is what the
/// formal is declared to hold.
///
/// Both are read POSITIVELY.  An enum tag counts only when the formal is
/// declared with an enum type; a string only when the argument really is a
/// string literal.  Neither is inferred from the formal's name, and an
/// argument this engine cannot read is no value at all rather than a
/// guessed one.
fn boundValueOfArgument(
    analyser: *Analyser,
    options: ResolveOptions,
    declared: Type,
    arg: Ast.Node.Index,
) Error!?BoundValue {
    const tree = &options.node_handle.handle.document.tree;
    switch (tree.nodeTag(arg)) {
        .enum_literal => {
            // A literal `.value` IS a known enum tag, whatever the formal is
            // DECLARED with.  That matters because a synthesized enum —
            // `meta.FieldEnum(Elem)`, which is `@Enum` over a type with no
            // AST behind it — has no enum type this engine can read, and
            // demanding one would skip exactly the bindings the acceptance
            // is about.  Nothing here is a runtime field guess.
            //
            // The enum is copied into the analyser arena so the binding's
            // owner is the arena rather than a parameter slot or a map
            // bucket that a later frame may reuse.
            const enum_ty: Type = if (declared.isEnumType()) declared else .unknown_type;
            const raw = tree.tokenSlice(tree.nodeMainToken(arg));

            // A plain `.value` is already its own name and borrows the
            // source.  A quoted tag — `@"v\x61lue"` — is a string literal
            // with an `@` in front, so it is decoded by the SAME canonical
            // parser every other string here uses; stripping only the `@`
            // and the quotes and taking the rest raw would leave the escape
            // sequence in the name.
            const quoted = raw.len >= 2 and raw[0] == '@' and raw[1] == '"';
            const name = if (quoted)
                (std.zig.string_literal.parseAlloc(analyser.arena, raw[2 .. raw.len - 1]) catch |err| switch (err) {
                    error.InvalidLiteral => return null,
                    error.OutOfMemory => return error.OutOfMemory,
                })
            else
                raw;

            return .{ .enum_tag = .{
                .name = name,
                .enum_ty = (try analyser.allocType(enum_ty)).*,
            } };
        },
        .string_literal => {
            const text = (try analyser.resolveStringLiteral(options.at(arg))) orelse return null;
            return .{ .string = text };
        },
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            // `@tagName(field)` as an ACTUAL argument evaluates to a string
            // through the same canonical evaluator that answers it anywhere
            // else, so the callee binds those bytes.
            const text = (try analyser.resolveStringLiteral(options.at(arg))) orelse return null;
            return .{ .string = text };
        },
        .identifier => {
            // FORWARDING.  `Self.items(field)` -> `self.slice().items(field)`
            // -> `FieldType(field)`: the inner callee is handed the CALLER's
            // formal by name, never a literal.  The value it should carry
            // is the one THIS frame already bound, read through the
            // declaration that name resolves to — a transferred copy of that
            // value, not a guess from the spelling and not a read of the
            // callee's own still-unbound parameter.
            //
            // The name resolves in the caller's frame: the declaration it
            // names lives in the caller's body, so only the caller's own
            // container carries the binding.  A container-free lookup finds
            // the declaration but no frame, and answers nothing.
            const handle = options.node_handle.handle;
            const name_token = ast.identifierTokenFromIdentifierNode(tree, arg) orelse return null;
            const name = offsets.identifierTokenToNameSlice(tree, name_token);
            const scoped = (try analyser.lookupSymbolGlobalScoped(handle, name, tree.tokenStart(name_token))) orelse return null;
            const framed = try withEnclosingContainer(options, scoped);
            const source = framed.container_type orelse return null;
            const info = switch (source.data) {
                .container => |info| info,
                else => return null,
            };
            return info.bound_values.get(.{
                .token = framed.decl.nameToken(&framed.handle.document.tree),
                .handle = framed.handle,
            });
        },
        else => return null,
    }
}

/// A container is the only thing in this engine that can CARRY an
/// instantiation, because `bound_params` is where a declaration's actual
/// arguments live.  Anything that is not a container has nowhere to put
/// them and is returned unchanged — a refusal, not a guess.
fn withBoundParams(
    analyser: *Analyser,
    ty: Type,
    bindings: TokenToTypeMap,
    values: BoundValueMap,
) Error!Type {
    if (bindings.count() == 0 and values.count() == 0) return ty;
    const info = switch (ty.data) {
        .container => |info| info,
        else => return ty,
    };
    var bound_params = try info.bound_params.clone(analyser.arena);
    for (bindings.keys(), bindings.values()) |token_handle, value| {
        try bound_params.put(analyser.arena, token_handle, value);
    }
    // Values ride along untouched: an enum tag's name and a string's bytes
    // are the ACTUALS this call supplied, and substituting a generic never
    // rewrites them.
    var bound_values = info.bound_values;
    for (values.keys(), values.values()) |token_handle, value| {
        try bound_values.put(analyser.arena, token_handle, value);
    }
    return .{
        .data = .{ .container = .{
            .scope_handle = info.scope_handle,
            .bound_params = bound_params,
            .bound_values = bound_values,
        } },
        .is_type_val = ty.is_type_val,
    };
}

/// The type this call RETURNS, carrying the instantiation's actual
/// argument values on it.
///
/// `Sha2x32(iv224, 224)` and `Sha2x32(iv256, 256)` both return the ONE
/// `struct { … }` declaration written inside `fn Sha2x32`.  Without this
/// the two instantiations are a single type, so the two extents cannot
/// both exist and whichever was resolved first answers for both.
///
/// A factory returning anything other than a container has nowhere to
/// carry its bindings and publishes nothing; that is a refusal, not a
/// guess.
fn instantiatedReturnValue(
    analyser: *Analyser,
    func_info: Type.Data.Function,
    bindings: TokenToTypeMap,
    values: BoundValueMap,
) Error!*Type {
    if (bindings.count() == 0 and values.count() == 0) return func_info.return_value;
    return analyser.allocType(try withBoundParams(analyser, func_info.return_value.*, bindings, values));
}

/// Binds the ACTUAL value of `arg` to `param`, when the parameter is one
/// the callee reads at comptime and the argument resolves to an integer
/// constant that fits the parameter's declared type.
///
/// Nothing is bound otherwise, so an argument the engine cannot read
/// leaves the parameter exactly as unknown as it was.
/// `arg` is written in the CALLER's body, so it is read in the caller's
/// frame: `options` carries that container, while `func_handle` stays the
/// CALLEE's handle, because a binding is keyed by the token written in the
/// callee's own declaration.
fn bindComptimeParameterValue(
    analyser: *Analyser,
    options: ResolveOptions,
    bindings: *TokenToTypeMap,
    func_handle: DocumentStore.Handle,
    param: Type.Data.Parameter,
    arg: Ast.Node.Index,
) Error!void {
    if (!isComptimeReadableParameter(analyser, param)) return;
    const param_name_token = param.name_token orelse return;
    const declared = declaredTypeOf(param.type) orelse return;

    const argument_type = (try analyser.resolveTypeOfNodeInternal(options.at(arg))) orelse return;

    // A BOOLEAN argument is already an interned constant of its declared
    // type: both values exist in the pool and `ip.toInt` has nothing to say
    // about either.  Coercing it would be arithmetic on something that is
    // not a number, so it binds as the value it is — which is what makes
    // `take(true)` and `take(false)` two instantiations rather than one.
    if (analyser.ip.zigTypeTag(declared) == .bool) {
        const index = argument_type.ipIndex() orelse return;
        if (argument_type.is_type_val) return;
        if (analyser.ip.typeOf(index) != .bool_type) return;
        try bindings.put(analyser.arena, .{ .token = param_name_token, .handle = func_handle }, Type.fromIP(
            analyser,
            .bool_type,
            index,
        ));
        return;
    }
    const value_index = internedIntValueOf(analyser, argument_type) orelse return;

    var err_msg: ErrorMsg = undefined;
    const coerced = try analyser.ip.coerce(analyser.arena, declared, value_index, builtin.target, &err_msg);
    if (coerced == .none) return;
    if (analyser.ip.isUnknown(coerced)) return;
    if (!isInternedIntValue(analyser.ip, coerced)) return;

    // The coerced value must BE the argument.  A narrowing that changed
    // the number — wrapping, truncating — is not this parameter's value,
    // and binding it would let an extent name a number the source never
    // wrote.
    const argument_value = analyser.ip.toInt(value_index, i128) orelse return;
    const coerced_value = analyser.ip.toInt(coerced, i128) orelse return;
    if (argument_value != coerced_value) return;

    try bindings.put(analyser.arena, .{ .token = param_name_token, .handle = func_handle }, Type.fromIP(
        analyser,
        analyser.ip.typeOf(coerced),
        coerced,
    ));
}

/// The declaration node whose main token is `token` — the function a
/// `Type.Data.Function` was built from.
fn functionNodeForToken(tree: *const Ast, token: Ast.TokenIndex) ?Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi, .fn_decl => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.nodeMainToken(node) != token) continue;
        return node;
    }
    return null;
}

/// The callee's DECLARED return type, read again under `container`.
///
/// Used when the return type depends on a VALUE the call site bound:
/// `Slice.items(self, comptime field: Field) []FieldType(field)` builds
/// its return type from `@FieldType(Elem, @tagName(field))`, and the
/// first read happened with no tag bound — so `@tagName` resolved to
/// nothing and the whole return type was already unknown.  Substituting a
/// generic cannot repair that; it only rewrites placeholders that are
/// still there, and unknown is not a placeholder.
///
/// This is the same reading the first read did, given the container that
/// now carries the binding — the same two steps, so a re-read answer has
/// the same shape the first one produced.
fn reretypeReturnValueUnder(
    analyser: *Analyser,
    func_info: Type.Data.Function,
    container: Type,
) Error!?Type {
    const handle = func_info.handle;
    const tree = &handle.document.tree;
    const func_node = functionNodeForToken(tree, func_info.fn_token) orelse return null;

    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buffer, func_node) orelse return null;

    // A type function's VALUE is its body's return expression, not its
    // `@FieldType(Elem, @tagName(field))`, which resolves under no container
    // to nothing. Re-read it under the container that now carries the binding.
    if (isTypeFunction(tree, proto)) {
        if (tree.nodeTag(func_node) != .fn_decl) return null;
        const body = tree.nodeData(func_node).node_and_node[1];
        const return_node = findReturnStatement(tree, body) orelse return null;
        const return_expr = tree.nodeData(return_node).opt_node.unwrap() orelse return null;
        const child = (try analyser.resolveTypeOfNodeInternal(.{
            .node_handle = .of(return_expr, handle),
            .container_type = container,
        })) orelse return null;
        if (!child.is_type_val) return null;
        return try child.instanceTypeVal(analyser);
    }

    const return_node = proto.ast.return_type.unwrap() orelse return null;

    const child = (try analyser.resolveTypeOfNodeInternal(.{
        .node_handle = .of(return_node, handle),
        .container_type = container,
    })) orelse return null;
    if (!child.is_type_val) return null;

    if (ast.hasInferredError(tree, proto)) {
        const error_union = try Type.createErrorUnionType(analyser, null, child);
        return try error_union.instanceUnchecked(analyser);
    }
    return try child.instanceTypeVal(analyser);
}

/// The function `call` names, carrying the instantiation this call site
/// actually supplies.
///
/// `options` is the CALLER's frame and is required: the callee's arguments
/// are written in the caller's body, so reading them under the caller's
/// container is the difference between the argument the source passes and
/// whatever a container-free lookup happens to find.  Its
/// `node_handle.handle` is the call's own handle, so the two agree on
/// which document every argument is read in.
pub fn resolveFunctionTypeFromCall(
    analyser: *Analyser,
    options: ResolveOptions,
    call: Ast.full.Call,
    func_ty: Type,
) Error!Type {
    const base_info = func_ty.data.function;

    // Nothing to instantiate: neither a generic type nor a parameter
    // this call site could give a value to.
    //
    // A labeled BLOCK, not a labeled expression: a label on a boolean
    // expression cannot be broken to, and this loop is what has to decide.
    const nothing_to_instantiate = blk: {
        if (func_ty.isGenericType()) break :blk false;
        for (base_info.parameters) |param| {
            if (isComptimeReadableParameter(analyser, param)) break :blk false;
            // Deliberately WIDER than "a value can be read": a `comptime`
            // formal the engine cannot read an integer for — an enum tag, a
            // string — still has to reach the binding machinery rather than
            // being passed over here.
            if (isComptimeFormal(param)) break :blk false;
        }
        break :blk true;
    };
    if (nothing_to_instantiate) return func_ty;

    var meta_params: TokenToTypeMap = switch (base_info.container_type.data) {
        .container => |info| try info.bound_params.clone(analyser.arena),
        else => .empty,
    };
    errdefer meta_params.deinit(analyser.arena);

    // The container's OWN bindings, as they stand BEFORE this call
    // contributes anything.  `meta_params` is a clone into the arena, so
    // this still reads the untouched original.
    const declared_params = switch (base_info.container_type.data) {
        .container => |info| info.bound_params,
        else => TokenToTypeMap.empty,
    };

    // The container's OWN bound VALUES, before this call contributes any.
    var bound_values: BoundValueMap = switch (base_info.container_type.data) {
        .container => |info| try info.bound_values.clone(analyser.arena),
        else => .empty,
    };
    defer bound_values.deinit(analyser.arena);
    const declared_values = switch (base_info.container_type.data) {
        .container => |info| info.bound_values,
        else => BoundValueMap.empty,
    };

    // Bound by POSITION against the call's own arguments, so an instance
    // call — where the first parameter is the receiver — lines up.  The
    // arity test is the single authority on whether a receiver binds; this
    // only resolves the receiver in the caller's own frame.
    const has_self_param = call.ast.params.len + 1 == base_info.parameters.len and
        try analyser.isInstanceCall(options, call, func_ty);

    const parameters = base_info.parameters[@intFromBool(has_self_param)..];
    const arguments = call.ast.params;
    const min_len = @min(parameters.len, arguments.len);
    var value_params: TokenToTypeMap = .empty;
    defer value_params.deinit(analyser.arena);
    for (parameters[0..min_len], arguments[0..min_len]) |param, arg| {
        try bindComptimeParameterValue(analyser, options, &value_params, base_info.handle, param, arg);

        const param_name_token = param.name_token orelse continue;
        const param_type = param.type;
        if (!param_type.is_type_val) continue;

        const argument_type = (try analyser.resolveTypeOfNodeInternal(options.at(arg))) orelse continue;

        switch (param_type.data) {
            .ip_index => |info| {
                if (info.index == .type_type and argument_type.is_type_val) {
                    try meta_params.put(analyser.arena, .{ .token = param_name_token, .handle = base_info.handle }, argument_type);
                }
            },
            .anytype_parameter => |info| {
                // TWO bindings, both carried by this instantiation.
                //
                // Under the `anytype` KEYWORD: the TYPE of the argument,
                // which is what substituting an `.anytype_parameter` node
                // needs.  `resolveGeneric` asserts that result is a type,
                // so nothing less will do here.
                try meta_params.put(analyser.arena, info.token_handle, try argument_type.typeOf(analyser));

                // Under the formal's NAME: the ACTUAL value the call
                // passed, with the flags it really has.  Two arguments that
                // are both types share the keyword binding — both `typeOf`
                // to `type_type` — and would collapse into one
                // instantiation without this.  Reading a formal back must
                // not have to guess a flag either: this value already says
                // whether it is a type, an instance or a function.
                try value_params.put(analyser.arena, .{
                    .token = param_name_token,
                    .handle = base_info.handle,
                }, argument_type);
            },
            else => {},
        }

        // A `comptime` formal whose ACTUAL value has no `Type`
        // representation: an enum tag, or a string literal.  Both are
        // recorded under the formal's NAME — the one key the body reads them
        // back by — and only when the argument is POSITIVELY that kind of
        // literal and the formal says so.  A value this engine cannot read
        // is no value at all, never one guessed from the formal's name.
        if (isComptimeFormal(param) or param_type.data == .anytype_parameter) {
            if (try boundValueOfArgument(analyser, options, param_type, arg)) |actual| {
                try bound_values.put(analyser.arena, .{
                    .token = param_name_token,
                    .handle = base_info.handle,
                }, actual);
            }
        }
    }

    // Everything this call site bound, as ONE map.  A parameter is either
    // declared `comptime T: type` or `comptime n: usize`, never both, so a
    // value binding can never shadow a meta binding.
    for (value_params.keys(), value_params.values()) |token_handle, value| {
        try meta_params.put(analyser.arena, token_handle, value);
    }

    // Did this call actually CHANGE the bindings?  Counting is not enough:
    // re-binding a formal the container already binds replaces a value
    // without changing how many there are, and leaving the previous value
    // in place would answer this call with the OTHER instantiation's
    // arguments — which is exactly a generic function reached again from
    // inside a frame that is already bound.  A call that adds nothing and
    // replaces nothing rebuilds nothing.
    const rebound = blk: {
        for (meta_params.keys(), meta_params.values()) |token_handle, value| {
            const previous = declared_params.get(token_handle) orelse break :blk true;
            if (!previous.eql(value)) break :blk true;
        }
        for (bound_values.keys(), bound_values.values()) |token_handle, value| {
            const previous = declared_values.get(token_handle) orelse break :blk true;
            if (!previous.eql(value)) break :blk true;
        }
        break :blk false;
    };

    // Record those bindings on BOTH things the callee is reached through.
    // Substituting a generic only rewrites values that are already there —
    // it never invents a key — so a `comptime T: type` the container never
    // declared stays unresolved unless it is written down here.  On the
    // return value that is the published instantiation; on the container
    // it is what lets any name read inside the callee's own body resolve
    // under the same arguments this call passed.
    var instantiated = func_ty;
    if (rebound) {
        var func_info = base_info;
        func_info.container_type = try analyser.allocType(try withBoundParams(
            analyser,
            base_info.container_type.*,
            meta_params,
            bound_values,
        ));
        func_info.return_value = try instantiatedReturnValue(analyser, base_info, meta_params, bound_values);
        // A return type can DEPEND ON A VALUE this call just bound —
        // `Slice.items(self, comptime field: Field) []FieldType(field)`
        // builds its return type out of `@FieldType(Elem,
        // @tagName(field))`.  Substituting generics cannot repair that: a
        // `@tagName` with no tag bound resolves to nothing at all, and the
        // return type has already been memoised as unknown.  So it is read
        // AGAIN, now that the binding exists, under the container that
        // carries it.
        if (bound_values.count() != 0) {
            if (try analyser.reretypeReturnValueUnder(
                func_info,
                func_info.container_type.*,
            )) |retyped| {
                func_info.return_value = try analyser.allocType(retyped);
            }
        }
        instantiated.data.function = func_info;
    }

    return try analyser.resolveGenericType(instantiated, meta_params);
}

const BreakIterator = struct {
    walker: ast.Walker,
    label: ?[]const u8,
    allow_unlabeled: bool,
    loop_depth: u32 = 0,

    fn next(
        it: *BreakIterator,
        allocator: std.mem.Allocator,
        tree: *const Ast,
    ) error{OutOfMemory}!?Ast.Node.Index {
        while (true) {
            const event = try it.walker.next(allocator, tree) orelse return null;
            switch (event) {
                .open => |node| switch (tree.nodeTag(node)) {
                    .@"break" => {
                        const opt_label_token, const opt_operand = tree.nodeData(node).opt_token_and_opt_node;
                        const operand = opt_operand.unwrap() orelse {
                            // TODO this is wrong! No operand implies `{}` i.e `void`.
                            continue;
                        };

                        if (it.label) |label| {
                            const label_token = opt_label_token.unwrap() orelse continue;
                            if (!std.mem.eql(u8, label, offsets.identifierTokenToNameSlice(tree, label_token))) continue;
                            return operand;
                        }

                        if (it.allow_unlabeled and it.loop_depth == 0 and opt_label_token == .none) {
                            return operand;
                        }
                    },

                    .@"while",
                    .while_simple,
                    .while_cont,
                    .@"for",
                    .for_simple,
                    => {
                        if (it.label == null) {
                            // We can ignore the inner loop
                            it.walker.skip();
                            continue;
                        }
                        it.loop_depth += 1;
                    },
                    else => {},
                },
                .close => |node| switch (tree.nodeTag(node)) {
                    .@"while",
                    .while_simple,
                    .while_cont,
                    .@"for",
                    .for_simple,
                    => {
                        it.loop_depth -= 1;
                    },
                    else => {},
                },
            }
        }
    }
};

pub fn resolveInstanceOfNode(analyser: *Analyser, options: ResolveOptions) Error!?Type {
    const ty = try analyser.resolveTypeOfNode(options) orelse return null;
    return ty.instanceTypeVal(analyser);
}

/// Resolves the type of an Ast Node.
/// Returns `null` if the type could not be resolved.
pub fn resolveTypeOfNode(analyser: *Analyser, options: ResolveOptions) Error!?Type {
    const binding = try analyser.resolveBindingOfNode(options) orelse return null;
    return binding.type;
}

fn resolveTypeOfNodeInternal(analyser: *Analyser, options: ResolveOptions) Error!?Type {
    const binding = try analyser.resolveBindingOfNodeInternal(options) orelse return null;
    return binding.type;
}

pub fn resolveBindingOfNode(analyser: *Analyser, options: ResolveOptions) Error!?Binding {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    return analyser.resolveBindingOfNodeInternal(options);
}

fn resolveBindingOfNodeInternal(analyser: *Analyser, options: ResolveOptions) Error!?Binding {
    const node_handle = options.node_handle;
    const node_with_uri: NodeWithUri = .{
        .node = node_handle.node,
        .uri = node_handle.handle.document.uri,
        .module = node_handle.handle.module,
        .comptime_values = analyser.comptime_values,
        .container_type = options.container_type,
    };
    const gop = try analyser.resolved_nodes.getOrPut(analyser.gpa, node_with_uri);
    if (gop.found_existing) return gop.value_ptr.*;

    // we insert null before resolving the type so that a recursive definition doesn't result in an infinite loop
    gop.value_ptr.* = null;

    const binding = try analyser.resolveBindingOfNodeUncached(options);
    if (binding != null) {
        analyser.resolved_nodes.getPtr(node_with_uri).?.* = binding;
    }

    return binding;
}

fn resolveTypeOfNodeUncached(analyser: *Analyser, options: ResolveOptions) Error!?Type {
    const node_handle = options.node_handle;
    const node = node_handle.node;
    const handle = node_handle.handle;
    const tree = &handle.document.tree;

    switch (tree.nodeTag(node)) {
        .global_var_decl,
        .local_var_decl,
        .simple_var_decl,
        .aligned_var_decl,
        => {
            const var_decl = tree.fullVarDecl(node).?;
            const mut_token_tag = tree.tokenTag(var_decl.ast.mut_token);
            var fallback_type: ?Type = null;

            if (var_decl.ast.type_node.unwrap()) |type_node| blk: {
                const decl_type = try analyser.resolveTypeOfNodeInternal(options.at(type_node)) orelse break :blk;
                if (decl_type.isMetaType()) {
                    fallback_type = .unknown_type;
                    break :blk;
                }
                if (mut_token_tag == .keyword_const) num: {
                    const init_node = var_decl.ast.init_node.unwrap() orelse break :num;
                    const ip_ty = decl_type.ipIndex() orelse break :num;
                    const ip_index = try analyser.resolveCoercedIPValue(ip_ty, options.at(init_node)) orelse break :num;
                    return Type.fromIP(analyser, analyser.ip.typeOf(ip_index), ip_index);
                }
                return try decl_type.instanceTypeVal(analyser);
            }

            if (var_decl.ast.init_node.unwrap()) |init_node| blk: {
                const ty = try analyser.resolveTypeOfNodeInternal(options.at(init_node)) orelse break :blk;
                if (mut_token_tag == .keyword_var)
                    return ty.withoutIPIndex(analyser);
                return ty;
            }

            return fallback_type;
        },
        .call,
        .call_comma,
        .call_one,
        .call_one_comma,
        => {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node).?;

            const ty = try analyser.resolveTypeOfNodeInternal(options.at(call.ast.fn_expr)) orelse return null;
            var func_ty = try analyser.resolveFuncProtoOfCallable(ty) orelse return null;
            if (func_ty.is_type_val) return null;

            func_ty = try analyser.resolveFunctionTypeFromCall(options.at(call.ast.fn_expr), call, func_ty);
            const func_info = func_ty.data.function;
            const func_uri = func_info.handle.document.uri.raw;

            if (std.mem.endsWith(u8, func_uri, "/std/meta.zig") and func_info.name != null) {
                const func_name = func_info.name.?;

                if (std.mem.eql(u8, func_name, "ArgsTuple")) {
                    if (call.ast.params.len < 1) return .unknown_type;
                    const arg = call.ast.params[0];
                    const arg_ty = try analyser.resolveTypeOfNodeInternal(options.at(arg)) orelse return .unknown_type;
                    if (!arg_ty.is_type_val or arg_ty.data != .function) return .unknown_type;
                    const arg_func_info = arg_ty.data.function;
                    if (arg_func_info.has_varargs) return .unknown_type;
                    const arg_func_params = arg_func_info.parameters;
                    const elem_ty_slice = try analyser.arena.alloc(Type, arg_func_params.len);
                    for (arg_func_params, elem_ty_slice) |param, *elem_ty| {
                        if (param.type.data == .anytype_parameter) return .unknown_type;
                        elem_ty.* = param.type;
                    }
                    return try Type.createTupleType(analyser, elem_ty_slice);
                }

                if (std.mem.eql(u8, func_name, "Tag")) {
                    if (call.ast.params.len < 1) return .unknown_type;
                    const arg = call.ast.params[0];
                    const arg_ty = try analyser.resolveTypeOfNodeInternal(options.at(arg)) orelse return .unknown_type;
                    // TODO: handle enum tag, e.g. `enum(u8)`
                    const tag_type = try analyser.resolveUnionTag(arg_ty) orelse return .unknown_type;
                    return try tag_type.typeOf(analyser);
                }
            }

            return func_info.return_value.*;
        },
        .container_field,
        .container_field_init,
        .container_field_align,
        => {
            const container_type = options.container_type orelse try analyser.innermostContainer(handle, tree.tokenStart(tree.firstToken(node)));
            if (container_type.isEnumType())
                return try container_type.instanceTypeVal(analyser);

            var field = tree.fullContainerField(node).?;

            if (container_type.isTaggedUnion()) {
                field.convertToNonTupleLike(tree);
                if (field.ast.type_expr == .none)
                    return Type.fromIP(analyser, .void_type, null);
            }

            const base = field.ast.type_expr.unwrap().?;
            const base_type = (try analyser.resolveTypeOfNodeInternal(options.at(base))) orelse return null;
            return try base_type.instanceTypeVal(analyser);
        },
        .@"comptime",
        .@"nosuspend",
        => return try analyser.resolveTypeOfNodeInternal(options.at(tree.nodeData(node).node)),
        .grouped_expression,
        => return try analyser.resolveTypeOfNodeInternal(options.at(tree.nodeData(node).node_and_token[0])),
        .struct_init,
        .struct_init_comma,
        .struct_init_one,
        .struct_init_one_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&buffer, node).?;

            const type_expr = struct_init.ast.type_expr.unwrap().?;
            const lhs = try analyser.resolveTypeOfNodeInternal(options.at(type_expr)) orelse return null;

            if (lhs.data == .array and lhs.data.array.elem_count == null) {
                var ty = lhs;
                ty.data.array.elem_count = struct_init.ast.fields.len;
                return try ty.instanceTypeVal(analyser);
            }
            return try lhs.instanceTypeVal(analyser);
        },
        .unwrap_optional => {
            const lhs_node, _ = tree.nodeData(node).node_and_token;

            const base_type = try analyser.resolveTypeOfNodeInternal(options.at(lhs_node)) orelse return null;

            return try analyser.resolveOptionalUnwrap(base_type);
        },
        .@"orelse" => {
            const lhs_node, const rhs_node = tree.nodeData(node).node_and_node;

            const lhs = try analyser.resolveTypeOfNodeInternal(options.at(lhs_node)) orelse return null;

            const rhs = try analyser.resolveTypeOfNodeInternal(options.at(rhs_node)) orelse return try analyser.resolveOptionalUnwrap(lhs);

            return try analyser.resolveOrelseType(lhs, rhs);
        },
        .@"catch" => {
            const lhs_node, _ = tree.nodeData(node).node_and_node;

            const lhs = try analyser.resolveTypeOfNodeInternal(options.at(lhs_node)) orelse return null;

            return try analyser.resolveUnwrapErrorUnionType(lhs, .payload);
        },
        .@"try" => {
            const expr_node = tree.nodeData(node).node;

            const base_type = try analyser.resolveTypeOfNodeInternal(options.at(expr_node)) orelse return null;

            return try analyser.resolveUnwrapErrorUnionType(base_type, .payload);
        },
        .optional_type => {
            const expr_node = tree.nodeData(node).node;

            const child_ty = try analyser.resolveTypeOfNodeInternal(options.at(expr_node)) orelse return null;
            if (!child_ty.is_type_val) return null;

            return try Type.createOptionalType(analyser, child_ty);
        },
        .ptr_type_aligned,
        .ptr_type_sentinel,
        .ptr_type,
        .ptr_type_bit_range,
        => {
            const ptr_info = ast.fullPtrType(tree, node).?;
            const size = ptr_info.size;
            const is_const = ptr_info.const_token != null;

            const sentinel = try analyser.resolveOptionalIPValue(options, ptr_info.ast.sentinel);

            const elem_resolved = try analyser.resolveTypeOfNodeInternal(options.at(ptr_info.ast.child_type)) orelse return null;
            // A type annotation names a type, but the element may resolve
            // as the container instance the frame carries — `@This()`
            // under an instantiated container.  Its type is the same
            // data with the type flag set, which is what a pointer is
            // built from; anything that is neither is still unknown.
            const elem_ty = if (elem_resolved.is_type_val) elem_resolved else try elem_resolved.typeOf(analyser);

            return try Type.createPointerType(analyser, size, sentinel, is_const, elem_ty);
        },
        .array_type,
        .array_type_sentinel,
        => {
            const array_info = tree.fullArrayType(node).?;

            const elem_count = try analyser.resolveIntegerLiteral(u64, options.at(array_info.ast.elem_count));
            const sentinel = try analyser.resolveOptionalIPValue(options, array_info.ast.sentinel);

            const elem_ty = try analyser.resolveTypeOfNodeInternal(options.at(array_info.ast.elem_type)) orelse return null;
            if (!elem_ty.is_type_val) return null;

            return try Type.createArrayType(analyser, elem_count, sentinel, elem_ty);
        },
        .array_init_one,
        .array_init_one_comma,
        .array_init_dot_two,
        .array_init_dot_two_comma,
        .array_init_dot,
        .array_init_dot_comma,
        .array_init,
        .array_init_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const array_init_info = tree.fullArrayInit(&buffer, node).?;

            if (array_init_info.ast.type_expr.unwrap()) |type_expr| blk: {
                const array_ty = try analyser.resolveTypeOfNode(options.at(type_expr)) orelse break :blk;
                if (array_ty.data == .array and array_ty.data.array.elem_count == null) {
                    var ty = array_ty;
                    ty.data.array.elem_count = array_init_info.ast.elements.len;
                    return try ty.instanceTypeVal(analyser);
                }
                return try array_ty.instanceTypeVal(analyser);
            }

            const elem_ty_slice = try analyser.arena.alloc(Type, array_init_info.ast.elements.len);
            for (elem_ty_slice, array_init_info.ast.elements) |*elem_ty, element| {
                elem_ty.* = try analyser.resolveTypeOfNodeInternal(options.at(element)) orelse return null;
                elem_ty.* = try elem_ty.typeOf(analyser);
            }
            const tuple_ty = try Type.createTupleType(analyser, elem_ty_slice);
            return try tuple_ty.instanceUnchecked(analyser);
        },
        .error_union => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;

            const error_set = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (!error_set.is_type_val) return null;

            const payload = try analyser.resolveTypeOfNodeInternal(options.at(rhs)) orelse return null;
            if (!payload.is_type_val) return null;

            return try Type.createErrorUnionType(analyser, error_set, payload);
        },

        .merge_error_sets => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            const lhs_index = try analyser.resolveErrorSetIPIndex(options.at(lhs)) orelse return null;
            const rhs_index = try analyser.resolveErrorSetIPIndex(options.at(rhs)) orelse return null;
            const ip_index = try analyser.ip.errorSetMerge(lhs_index, rhs_index);
            return Type.fromIP(analyser, .type_type, ip_index);
        },

        .error_set_decl => {
            const lbrace, const rbrace = tree.nodeData(node).token_and_token;
            var strings: std.array_hash_map.Auto(InternPool.String, void) = .empty;
            defer strings.deinit(analyser.gpa);
            var i: usize = 0;
            for (lbrace + 1..rbrace) |tok_i| {
                if (tree.tokenTag(@intCast(tok_i)) != .identifier) continue;
                const identifier_token: Ast.TokenIndex = @intCast(tok_i);
                defer i += 1;
                const name = offsets.tokenToSlice(tree, identifier_token);
                const index = try analyser.ip.string_pool.getOrPutString(analyser.store.io, analyser.gpa, name);
                try strings.put(analyser.gpa, index, {});
            }
            const names = try analyser.ip.getStringSlice(strings.keys());
            const ip_index = try analyser.ip.get(.{ .error_set_type = .{ .owner_decl = .none, .names = names } });
            return Type.fromIP(analyser, .type_type, ip_index);
        },

        .container_decl,
        .container_decl_arg,
        .container_decl_arg_trailing,
        .container_decl_trailing,
        .container_decl_two,
        .container_decl_two_trailing,
        .tagged_union,
        .tagged_union_trailing,
        .tagged_union_two,
        .tagged_union_two_trailing,
        .tagged_union_enum_tag,
        .tagged_union_enum_tag_trailing,
        => |tag| {
            not_a_tuple: {
                switch (tag) {
                    .container_decl,
                    .container_decl_trailing,
                    .container_decl_two,
                    .container_decl_two_trailing,
                    => {},
                    else => break :not_a_tuple,
                }

                var buffer: [2]Ast.Node.Index = undefined;
                const container_decl = tree.fullContainerDecl(&buffer, node).?;
                if (container_decl.ast.members.len == 0) break :not_a_tuple; // technically a tuple
                if (tree.tokenTag(container_decl.ast.main_token) != .keyword_struct) break :not_a_tuple;
                const elem_ty_slice = try analyser.arena.alloc(Type, container_decl.ast.members.len);

                var has_unresolved_fields = false;
                for (elem_ty_slice, container_decl.ast.members) |*elem_ty, member_node| {
                    const container_field = tree.fullContainerField(member_node) orelse break :not_a_tuple;
                    if (!container_field.ast.tuple_like) break :not_a_tuple;
                    const type_expr = container_field.ast.type_expr.unwrap().?;
                    elem_ty.* = try analyser.resolveTypeOfNodeInternal(options.at(type_expr)) orelse {
                        has_unresolved_fields = true;
                        continue;
                    };
                }

                if (has_unresolved_fields) return null;
                return try Type.createTupleType(analyser, elem_ty_slice);
            }

            return try analyser.innermostContainer(handle, tree.tokenStart(tree.firstToken(node)));
        },
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, node).?;

            const call_name = tree.tokenSlice(tree.nodeMainToken(node));

            const item = std.zig.BuiltinFn.list.get(call_name) orelse return null;
            switch (item.tag) {
                .This => {
                    if (params.len != 0) return null;
                    return options.container_type orelse try analyser.innermostContainer(handle, tree.tokenStart(tree.firstToken(node)));
                },
                .int_cast, .int_from_float, .float_cast, .float_from_int, .bit_cast => {
                    if (params.len != 1) return null;
                    const source_index = tree.tokenStart(tree.nodeMainToken(node));
                    const lineage = try ast.nodesOverlappingIndex(analyser.arena, tree, source_index);
                    defer analyser.arena.free(lineage);
                    if (lineage.len > 128) return null;
                    const index = std.mem.findScalar(Ast.Node.Index, lineage, node) orelse return null;
                    return analyser.resolveExpressionTypeFromAncestors(options.at(node), node, lineage[index + 1 ..]);
                },
                .as => {
                    if (params.len < 1) return null;
                    const ty = (try analyser.resolveTypeOfNodeInternal(options.at(params[0]))) orelse return null;
                    num: {
                        if (params.len < 2) break :num;
                        const ip_ty = ty.ipIndex() orelse break :num;
                        const ip_index = try analyser.resolveCoercedIPValue(ip_ty, options.at(params[1])) orelse break :num;
                        return Type.fromIP(analyser, analyser.ip.typeOf(ip_index), ip_index);
                    }
                    return try ty.instanceTypeVal(analyser);
                },
                .atomic_load,
                .atomic_rmw,
                .@"extern",
                .mul_add,
                .union_init,
                => {
                    if (params.len < 1) return null;
                    const ty = (try analyser.resolveTypeOfNodeInternal(options.at(params[0]))) orelse return null;
                    return try ty.instanceTypeVal(analyser);
                },

                .c_va_arg => {
                    if (params.len < 2) return null;
                    const ty = (try analyser.resolveTypeOfNodeInternal(options.at(params[1]))) orelse return null;
                    return try ty.instanceTypeVal(analyser);
                },
                .sqrt,
                .sin,
                .cos,
                .tan,
                .exp,
                .exp2,
                .log,
                .log2,
                .log10,
                .floor,
                .ceil,
                .trunc,
                .round,
                => {
                    if (params.len != 1) return null;
                    const ty = (try analyser.resolveTypeOfNodeInternal(options.at(params[0]))) orelse return null;
                    const payload = switch (ty.data) {
                        .ip_index => |payload| payload,
                        else => return null,
                    };
                    if (!analyser.ip.isFloat(analyser.ip.scalarType(payload.type))) return null;
                    return Type.fromIP(analyser, payload.type, null);
                },
                .abs => {
                    if (params.len != 1) return null;

                    const ty = try analyser.resolveTypeOfNodeInternal(options.at(params[0])) orelse return null;

                    const payload = switch (ty.data) {
                        .ip_index => |payload| payload,
                        else => return null,
                    };

                    // Based on Sema.zirAbs
                    const operand_ty = payload.type;
                    const scalar_ty = analyser.ip.scalarType(operand_ty);
                    const scalar_tag = analyser.ip.zigTypeTag(scalar_ty) orelse return null;
                    const result_ty = switch (scalar_tag) {
                        .comptime_float, .float, .comptime_int => operand_ty,
                        .int => if (analyser.ip.isSignedInt(scalar_ty, builtin.target))
                            try analyser.ip.toUnsigned(operand_ty, builtin.target)
                        else
                            operand_ty,
                        else => return null,
                    };

                    return Type.fromIP(analyser, result_ty, null);
                },
                .TypeOf => {
                    // TODO Do peer type resolution, we just keep the first for now.

                    if (params.len < 1) return null;
                    var resolved_type = (try analyser.resolveTypeOfNodeInternal(options.at(params[0]))) orelse return null;
                    return try resolved_type.typeOf(analyser);
                },
                .import => {
                    if (params.len == 0) return null;
                    const import_param = params[0];
                    if (tree.nodeTag(import_param) != .string_literal) return null;

                    const string_literal = tree.tokenSlice(tree.nodeMainToken(import_param));
                    const import_string = string_literal[1 .. string_literal.len - 1];
                    if (std.mem.endsWith(u8, import_string, ".zon")) {
                        // TODO
                        return null;
                    }

                    if (try analyser.resolveImportString(handle, import_string)) |ty| return ty;
                    // A relative import belongs to its defining document.
                    if (std.mem.endsWith(u8, import_string, ".zig")) return null;
                    if (try analyser.resolveImportString(analyser.root_handle orelse return null, import_string)) |ty| return ty;
                    return null;
                },
                .FieldType => {
                    if (params.len < 2) return null;

                    const container_type = (try analyser.resolveTypeOfNodeInternal(options.at(params[0]))) orelse return null;
                    const instance = try container_type.instanceTypeVal(analyser) orelse return null;

                    const field_name = try analyser.resolveStringLiteral(options.at(params[1])) orelse return null;

                    const field = try instance.lookupSymbol(analyser, field_name) orelse return null;
                    const result = try field.resolveType(analyser) orelse return null;
                    return try result.typeOf(analyser);
                },
                .field => {
                    if (params.len < 2) return null;

                    const lhs = (try analyser.resolveTypeOfNodeInternal(options.at(params[0]))) orelse return null;

                    const field_name = try analyser.resolveStringLiteral(options.at(params[1])) orelse return null;

                    return try analyser.resolveFieldAccess(lhs, field_name);
                },
                .compile_error => {
                    return .{ .data = .{ .compile_error = node_handle }, .is_type_val = false };
                },
                .EnumLiteral => {
                    return Type.fromIP(analyser, .type_type, .enum_literal_type);
                },
                .Vector => {
                    if (params.len != 2) return null;

                    const child_ty = try analyser.resolveTypeOfNodeInternal(options.at(params[1])) orelse return null;
                    if (!child_ty.is_type_val) return null;

                    const child_ty_ip_index = switch (child_ty.data) {
                        .ip_index => |payload| payload.index orelse try analyser.ip.getUnknown(payload.type),
                        else => return null,
                    };

                    const len = try analyser.resolveIntegerLiteral(u32, options.at(params[0])) orelse
                        return null; // `InternPool.Key.Vector.len` can't represent unknown length yet

                    const vector_ty_ip_index = try analyser.ip.get(.{
                        .vector_type = .{
                            .len = len,
                            .child = child_ty_ip_index,
                        },
                    });

                    return Type.fromIP(analyser, .type_type, vector_ty_ip_index);
                },
                else => {
                    const data = version_data.builtins.get(call_name) orelse return null;
                    return analyser.resolveLangrefType(data.return_type);
                },
            }
        },
        .fn_proto,
        .fn_proto_multi,
        .fn_proto_one,
        .fn_proto_simple,
        .fn_decl,
        => {
            var buf: [1]Ast.Node.Index = undefined;
            const fn_proto = tree.fullFnProto(&buf, node).?;

            const container_type = options.container_type orelse try analyser.innermostContainer(handle, tree.tokenStart(fn_proto.ast.fn_token));
            const doc_comments = try getDocComments(analyser.arena, tree, node);
            const name = if (fn_proto.name_token) |t| tree.tokenSlice(t) else null;

            var parameters: std.ArrayList(Type.Data.Parameter) = .empty;
            var has_varargs = false;

            var it: ast.FnParamIterator = .init(&fn_proto, tree);
            while (it.next()) |param| {
                if (has_varargs) {
                    return null;
                }

                var param_comments: ?[]const u8 = null;
                if (param.first_doc_comment) |dc| {
                    param_comments = try collectDocComments(analyser.arena, tree, dc, false);
                }

                var param_modifier: ?Type.Data.Parameter.Modifier = null;
                if (param.comptime_noalias) |token_index| {
                    switch (tree.tokenTag(token_index)) {
                        .keyword_comptime => param_modifier = .comptime_param,
                        .keyword_noalias => param_modifier = .noalias_param,
                        else => unreachable,
                    }
                }

                var param_name: ?[]const u8 = null;
                if (param.name_token) |name_token| {
                    param_name = tree.tokenSlice(name_token);
                }

                const param_type: Type = param_type: {
                    if (param.type_expr) |type_expr| blk: {
                        const ty = try analyser.resolveTypeOfNode(options.at(type_expr)) orelse {
                            break :blk;
                        };
                        if (!ty.is_type_val) {
                            break :blk;
                        }
                        break :param_type ty;
                    }
                    if (param.anytype_ellipsis3) |token_index| {
                        switch (tree.tokenTag(token_index)) {
                            .keyword_anytype => {
                                break :param_type .{
                                    .data = .{
                                        .anytype_parameter = .{
                                            .token_handle = .{ .token = token_index, .handle = handle },
                                            .type_from_callsite_references = null,
                                        },
                                    },
                                    .is_type_val = true,
                                };
                            },
                            .ellipsis3 => {
                                has_varargs = true;
                                continue;
                            },
                            else => unreachable,
                        }
                    }
                    break :param_type .unknown_type;
                };

                try parameters.append(analyser.arena, .{
                    .doc_comments = param_comments,
                    .modifier = param_modifier,
                    .name = param_name,
                    .name_token = param.name_token,
                    .type = param_type,
                });
            }

            const return_value = try analyser.resolveReturnValueOfFuncNode(handle, node) orelse
                Type.fromIP(analyser, .unknown_type, null);

            const info: Type.Data.Function = .{
                .handle = handle,
                .fn_token = fn_proto.ast.fn_token,
                .container_type = try analyser.allocType(container_type),
                .doc_comments = doc_comments,
                .name = name,
                .parameters = parameters.items,
                .has_varargs = has_varargs,
                .return_value = try analyser.allocType(return_value),
            };

            // This is a function type
            if (fn_proto.name_token == null) {
                return .{ .data = .{ .function = info }, .is_type_val = true };
            }

            return .{ .data = .{ .function = info }, .is_type_val = false };
        },
        .@"if", .if_simple => {
            const if_node = ast.fullIf(tree, node).?;

            var either_buffer: [2]Type.TypeWithDescriptor = undefined;
            var either: std.ArrayList(Type.TypeWithDescriptor) = .initBuffer(&either_buffer);

            if (try analyser.resolveTypeOfNodeInternal(options.at(if_node.ast.then_expr))) |t| {
                either.appendAssumeCapacity(.{ .type = t, .descriptor = offsets.nodeToSlice(tree, if_node.ast.cond_expr) });
            }
            if (if_node.ast.else_expr.unwrap()) |else_expr| {
                if (try analyser.resolveTypeOfNodeInternal(options.at(else_expr))) |t| {
                    either.appendAssumeCapacity(.{ .type = t, .descriptor = try std.fmt.allocPrint(analyser.arena, "!({s})", .{offsets.nodeToSlice(tree, if_node.ast.cond_expr)}) });
                }
            }
            return Type.fromEither(analyser, either.items);
        },
        .@"switch",
        .switch_comma,
        => {
            const switch_node = tree.switchFull(node);

            if (try narrowSwitchToMatchingProng(analyser, options, switch_node)) |narrowed|
                return narrowed;

            var either: std.ArrayList(Type.TypeWithDescriptor) = .empty;

            if (switch_node.label_token) |label_token| {
                var it: BreakIterator = .{
                    .walker = try .init(analyser.gpa, tree, node),
                    .label = offsets.identifierTokenToNameSlice(tree, label_token),
                    .allow_unlabeled = false,
                };
                defer it.walker.deinit(analyser.gpa);
                while (try it.next(analyser.gpa, tree)) |operand| {
                    if (try analyser.resolveTypeOfNodeInternal(options.at(operand))) |operand_type| {
                        try either.append(analyser.arena, .{
                            .type = operand_type,
                            .descriptor = "break",
                        });
                    }
                }
            }

            for (switch_node.ast.cases) |case| {
                const switch_case = tree.fullSwitchCase(case).?;
                var descriptor: std.ArrayList(u8) = .empty;

                for (switch_case.ast.values, 0..) |values, index| {
                    try descriptor.appendSlice(analyser.arena, offsets.nodeToSlice(tree, values));
                    if (index != switch_case.ast.values.len - 1) try descriptor.appendSlice(analyser.arena, ", ");
                }

                if (try analyser.resolveTypeOfNodeInternal(options.at(switch_case.ast.target_expr))) |t|
                    try either.append(analyser.arena, .{
                        .type = t,
                        .descriptor = try descriptor.toOwnedSlice(analyser.arena),
                    });
            }

            return Type.fromEither(analyser, either.items);
        },
        .@"while",
        .while_simple,
        .while_cont,
        .@"for",
        .for_simple,
        => {
            const loop: struct {
                label_token: ?Ast.TokenIndex,
                then_expr: Ast.Node.Index,
                else_expr: Ast.Node.OptionalIndex,
            } = if (ast.fullWhile(tree, node)) |while_node|
                .{
                    .label_token = while_node.label_token,
                    .then_expr = while_node.ast.then_expr,
                    .else_expr = while_node.ast.else_expr,
                }
            else if (ast.fullFor(tree, node)) |for_node|
                .{
                    .label_token = for_node.label_token,
                    .then_expr = for_node.ast.then_expr,
                    .else_expr = for_node.ast.else_expr,
                }
            else
                unreachable;

            const else_expr = loop.else_expr.unwrap() orelse return null;

            // TODO: peer type resolution based on `else` and all `break` statements
            if (try analyser.resolveTypeOfNodeInternal(options.at(else_expr))) |else_type|
                return else_type.withoutIPIndex(analyser);

            var it: BreakIterator = .{
                .walker = try .init(analyser.gpa, tree, loop.then_expr),
                .label = if (loop.label_token) |token| offsets.identifierTokenToNameSlice(tree, token) else null,
                .allow_unlabeled = true,
            };
            defer it.walker.deinit(analyser.gpa);

            while (try it.next(analyser.gpa, tree)) |operand| {
                if (try analyser.resolveTypeOfNodeInternal(options.at(operand))) |operand_type|
                    return operand_type;
            }
        },
        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const statements = tree.blockStatements(&buffer, node).?;
            if (statements.len == 0) {
                return Type.fromIP(analyser, .void_type, .void_value);
            }

            const label_token = ast.blockLabel(tree, node) orelse {
                const last_statement = statements[statements.len - 1];
                if (try analyser.resolveTypeOfNodeInternal(options.at(last_statement))) |ty| {
                    if ((try ty.typeOf(analyser)).isNoreturnType()) {
                        return Type.fromIP(analyser, .noreturn_type, null);
                    }
                }
                return Type.fromIP(analyser, .void_type, .void_value);
            };

            // TODO: peer type resolution based on all `break` statements
            var it: BreakIterator = .{
                .walker = try .init(analyser.gpa, tree, node),
                .label = offsets.identifierTokenToNameSlice(tree, label_token),
                .allow_unlabeled = false,
            };
            defer it.walker.deinit(analyser.gpa);

            while (try it.next(analyser.gpa, tree)) |operand| {
                if (try analyser.resolveTypeOfNodeInternal(options.at(operand))) |operand_type|
                    return operand_type.withoutIPIndex(analyser);
            }
        },

        .for_range => {},

        .equal_equal,
        .bang_equal,
        .less_than,
        .greater_than,
        .less_or_equal,
        .greater_or_equal,
        => {
            const lhs, _ = tree.nodeData(node).node_and_node;

            const rhs = tree.nodeData(node).node_and_node[1];

            // Two interned integer constants decide this comparison right
            // here.  `@sizeOf(T) == 0` is exactly this shape, and it is
            // the only way a comptime branch on a layout question gets an
            // answer: anything else — a pointer, a float, an unknown
            // layout — falls through to what the rest of this arm gives,
            // which is a type and not a decision.
            if (tree.nodeTag(node) == .equal_equal or tree.nodeTag(node) == .bang_equal) {
                const lhs_ty = try analyser.resolveTypeOfNodeInternal(options.at(lhs));
                const rhs_ty = try analyser.resolveTypeOfNodeInternal(options.at(rhs));
                if (lhs_ty != null and rhs_ty != null) {
                    if (internedIntValueOf(analyser, lhs_ty.?)) |lhs_value| {
                        if (internedIntValueOf(analyser, rhs_ty.?)) |rhs_value| {
                            if (analyser.ip.toInt(lhs_value, i128)) |lhs_int| {
                                if (analyser.ip.toInt(rhs_value, i128)) |rhs_int| {
                                    const equal = lhs_int == rhs_int;
                                    const want_equal = tree.nodeTag(node) == .equal_equal;
                                    return Type.fromIP(
                                        analyser,
                                        .bool_type,
                                        if (equal == want_equal) .bool_true else .bool_false,
                                    );
                                }
                            }
                        }
                    }
                }
            }

            const ty = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse
                return Type.fromIP(analyser, .bool_type, null);
            const typeof = try ty.typeOf(analyser);

            if (typeof.ipIndex()) |index| {
                const key = analyser.ip.indexToKey(index);
                if (key == .vector_type) {
                    const vector_ty_ip_index = try analyser.ip.get(.{
                        .vector_type = .{
                            .len = key.vector_type.len,
                            .child = .bool_type,
                        },
                    });

                    return Type.fromIP(analyser, vector_ty_ip_index, null);
                }
            }
            return Type.fromIP(analyser, .bool_type, null);
        },

        .bool_and,
        .bool_or,
        .bool_not,
        => return Type.fromIP(analyser, .bool_type, null),

        .bit_not,
        .negation,
        .negation_wrap,
        => {
            const ty = try analyser.resolveTypeOfNodeInternal(options.at(tree.nodeData(node).node)) orelse return null;
            if (ty.is_type_val) return null;
            return ty.withoutIPIndex(analyser);
        },

        .multiline_string_literal => {
            const start, const end = tree.nodeData(node).token_and_token;

            var length: u64 = 0;

            for (start..end + 1, 0..) |token_index, i| {
                const slice = tree.tokenSlice(@intCast(token_index));
                length += slice.len - 2 + @intFromBool(i != 0);
            }

            const string_literal_type = try analyser.ip.get(.{ .pointer_type = .{
                .elem_type = try analyser.ip.get(.{ .array_type = .{
                    .child = .u8_type,
                    .len = length,
                    .sentinel = .zero_u8,
                } }),
                .flags = .{
                    .size = .one,
                    .is_const = true,
                },
            } });
            return Type.fromIP(analyser, string_literal_type, null);
        },
        .string_literal => {
            const token_bytes = tree.tokenSlice(tree.nodeMainToken(node));

            var discarding_writer: std.Io.Writer.Discarding = .init(&.{});
            const result = std.zig.string_literal.parseWrite(&discarding_writer.writer, token_bytes) catch |err| switch (err) {
                error.WriteFailed => unreachable,
            };
            switch (result) {
                .success => {},
                .failure => return null,
            }

            const string_literal_type = try analyser.ip.get(.{ .pointer_type = .{
                .elem_type = try analyser.ip.get(.{ .array_type = .{
                    .child = .u8_type,
                    .len = discarding_writer.count,
                    .sentinel = .zero_u8,
                } }),
                .flags = .{
                    .size = .one,
                    .is_const = true,
                },
            } });
            return Type.fromIP(analyser, string_literal_type, null);
        },
        .error_value => {
            const name_token = tree.nodeMainToken(node) + 2;
            if (tree.tokenTag(name_token) != .identifier) return null;
            const name = offsets.identifierTokenToNameSlice(tree, name_token);
            const name_index = try analyser.ip.string_pool.getOrPutString(analyser.store.io, analyser.gpa, name);

            const error_set_type = try analyser.ip.get(.{ .error_set_type = .{
                .owner_decl = .none,
                .names = try analyser.ip.getStringSlice(&.{name_index}),
            } });
            const error_value = try analyser.ip.get(.{ .error_value = .{
                .ty = error_set_type,
                .error_tag_name = name_index,
            } });
            return Type.fromIP(analyser, error_set_type, error_value);
        },

        .char_literal => return Type.fromIP(analyser, .comptime_int_type, null),

        .number_literal => {
            const bytes = offsets.tokenToSlice(tree, tree.nodeMainToken(node));
            const result = std.zig.parseNumberLiteral(bytes);
            const ty: InternPool.Index = switch (result) {
                .int,
                .big_int,
                => .comptime_int_type,
                .float => .comptime_float_type,
                .failure => return null,
            };
            const value: ?InternPool.Index = switch (result) {
                .float => blk: {
                    break :blk try analyser.ip.get(
                        .{ .float_comptime_value = std.fmt.parseFloat(f128, bytes) catch break :blk null },
                    );
                },
                .int => |magnitude| blk: {
                    // `parseNumberLiteral` already scanned these bytes into
                    // the literal's magnitude, so the value comes from that
                    // scan instead of a second pass over the same text.
                    if (bytes[0] != '-') {
                        break :blk try analyser.ip.get(
                            .{ .int_u64_value = .{ .ty = ty, .int = magnitude } },
                        );
                    }
                    // A negative literal is stored as the value it denotes.
                    // `-(2^63)` is one past `maxInt(i64)` and still exactly
                    // representable; a magnitude past it is not, and keeps
                    // the type-only answer rather than a wrapped value that
                    // would name a different number than the source does.
                    const signed_limit: u64 = @as(u64, std.math.maxInt(i64)) + 1;
                    if (magnitude > signed_limit) break :blk null;
                    break :blk try analyser.ip.get(
                        .{ .int_i64_value = .{ .ty = ty, .int = if (magnitude == signed_limit)
                            std.math.minInt(i64)
                        else
                            -@as(i64, @intCast(magnitude)) } },
                    );
                },
                .big_int => |base| blk: {
                    var big_int: std.math.big.int.Managed = try .init(analyser.gpa);
                    defer big_int.deinit();
                    const prefix_length: usize = if (base != .decimal) 2 else 0;
                    big_int.setString(@intFromEnum(base), bytes[prefix_length..]) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => break :blk null,
                    };
                    std.debug.assert(ty == .comptime_int_type);
                    break :blk try analyser.ip.getBigInt(ty, big_int.toConst());
                },
                .failure => unreachable, // checked above
            };

            return if (value) |v| Type.fromIP(analyser, ty, v) else Type.fromIP(analyser, ty, null);
        },

        .enum_literal => {
            const source_token = tree.tokenStart(tree.nodeMainToken(node));
            const lineage = try ast.nodesOverlappingIndex(analyser.arena, tree, source_token);
            defer analyser.arena.free(lineage);
            const enclosing = lineage[1..]; // zbc-disable-line: slice-from-fixed-offset-without-len-check — enum_literal node is always nested; nodesOverlappingIndex returns len>=2

            const tag = offsets.identifierTokenToNameSlice(tree, tree.nodeMainToken(node));

            // A root enum literal in CALLEE position — `add(.submit(arena))`
            // — names a declaration of whatever container the call site
            // EXPECTS and then calls it.  Zig resolves that name against the
            // expected type and against nothing else, so the expected type is
            // the only sound basis, and `resolveExpressionType` already reads
            // it for this position.  A decl-literal test would be the wrong
            // question: it asks whether the declaration's value IS an instance
            // of the container, which is what `const x: Query = .someDecl;`
            // means and not what a call means — a call asks whether the
            // declaration is CALLABLE.
            //
            // Nothing but a call can put an enum literal in callee position in
            // valid Zig, so a callee this cannot place is an UNREADABLE
            // caller and answers `null`.  It must not answer
            // `enum_literal_type`: that is a positive "this is not a
            // function", which nothing here supports, and a consumer that
            // believes it omits a real caller instead of refusing on it.
            if (isCallCallee(tree, node, enclosing)) {
                const expected = (try analyser.resolveExpressionType(options.at(node), node, enclosing)) orelse return null;
                const callee = (try lookupEnumLiteralCallee(analyser, expected, tag)) orelse return null;
                return try callee.resolveType(analyser);
            }

            const decl, const type_maybe = (try analyser.lookupSymbolFieldInit(options.at(node), tag, node, enclosing)) orelse return Type.fromIP(analyser, .enum_literal_type, null);
            return type_maybe orelse decl.resolveType(analyser);
        },

        .unreachable_literal => return Type.fromIP(analyser, .noreturn_type, null),
        .anyframe_literal => return Type.fromIP(analyser, .anyframe_type, null),

        .anyframe_type => return .unknown_type,

        .mul,
        .div,
        .mod,
        .bit_and,
        .bit_xor,
        .bit_or,
        => |tag| {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            const lhs_valued = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (lhs_valued.is_type_val) return null;
            const rhs_valued = try analyser.resolveTypeOfNodeInternal(options.at(rhs)) orelse return null;
            if (rhs_valued.is_type_val) return null;
            const peer = try analyser.resolvePeerTypes(
                lhs_valued.withoutIPIndex(analyser),
                rhs_valued.withoutIPIndex(analyser),
            );
            const op = comptimeIntOpOf(tag) orelse return peer;
            return try analyser.withComptimeIntValue(op, peer orelse return null, lhs_valued, rhs_valued);
        },

        .mul_wrap,
        .mul_sat,
        .add_wrap,
        .sub_wrap,
        .add_sat,
        .sub_sat,
        => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            var lhs_ty = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (lhs_ty.is_type_val) return null;
            var rhs_ty = try analyser.resolveTypeOfNodeInternal(options.at(rhs)) orelse return null;
            if (rhs_ty.is_type_val) return null;
            lhs_ty = lhs_ty.withoutIPIndex(analyser);
            rhs_ty = rhs_ty.withoutIPIndex(analyser);
            return analyser.resolvePeerTypes(lhs_ty, rhs_ty);
        },

        .add => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            const lhs_valued = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (lhs_valued.is_type_val) return null;
            const rhs_valued = try analyser.resolveTypeOfNodeInternal(options.at(rhs)) orelse return null;
            if (rhs_valued.is_type_val) return null;
            const lhs_ty = lhs_valued.withoutIPIndex(analyser);
            const rhs_ty = rhs_valued.withoutIPIndex(analyser);
            if (lhs_ty.pointerSize(analyser)) |lhs_size| {
                return switch (lhs_size) {
                    .many, .c => lhs_ty,
                    else => null,
                };
            }
            const peer = try analyser.resolvePeerTypes(lhs_ty, rhs_ty) orelse return null;
            return try analyser.withComptimeIntValue(.add, peer, lhs_valued, rhs_valued);
        },

        .sub => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            const lhs_valued = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (lhs_valued.is_type_val) return null;
            const rhs_valued = try analyser.resolveTypeOfNodeInternal(options.at(rhs)) orelse return null;
            if (rhs_valued.is_type_val) return null;
            const lhs_ty = lhs_valued.withoutIPIndex(analyser);
            const rhs_ty = rhs_valued.withoutIPIndex(analyser);
            if (lhs_ty.pointerSize(analyser)) |lhs_size| {
                if (rhs_ty.pointerSize(analyser)) |rhs_size| {
                    if (lhs_size == .slice) return null;
                    if (rhs_size == .slice) return null;
                    return Type.fromIP(analyser, .usize_type, null);
                } else {
                    return switch (lhs_size) {
                        .many, .c => lhs_ty,
                        else => null,
                    };
                }
            }
            const peer = try analyser.resolvePeerTypes(lhs_ty, rhs_ty) orelse return null;
            return try analyser.withComptimeIntValue(.sub, peer, lhs_valued, rhs_valued);
        },

        .shl,
        .shl_sat,
        .shr,
        => {
            const lhs, _ = tree.nodeData(node).node_and_node;
            const lhs_ty = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (lhs_ty.is_type_val) return null;
            return lhs_ty.withoutIPIndex(analyser);
        },

        .array_mult => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            var array = try analyser.resolveTypeOfNodeInternal(options.at(lhs)) orelse return null;
            if (array.is_type_val) return null;
            const pointer = array.pointerElementType(analyser, .one);
            if (pointer) |pointee| array = try pointee.instanceUnchecked(analyser);
            const count, const sentinel, const elem_ty = array.arrayInfo(analyser) orelse return null;
            const repeat = try analyser.resolveIntegerLiteral(u64, options.at(rhs));
            const length: ?u64 = if (count != null and repeat != null)
                std.math.mul(u64, count.?, repeat.?) catch null
            else
                null;
            const array_ty = try Type.createArrayType(analyser, length, sentinel, elem_ty);
            if (pointer != null) {
                const pointer_ty = try Type.createPointerType(analyser, .one, .none, true, array_ty);
                return try pointer_ty.instanceUnchecked(analyser);
            }
            return try array_ty.instanceUnchecked(analyser);
        },

        .array_cat => {
            const l_elem_idx, const r_elem_idx = tree.nodeData(node).node_and_node;

            var l_elem_ty = try analyser.resolveTypeOfNodeInternal(options.at(l_elem_idx)) orelse return null;
            if (l_elem_ty.is_type_val) return null;

            var r_elem_ty = try analyser.resolveTypeOfNodeInternal(options.at(r_elem_idx)) orelse return null;
            if (r_elem_ty.is_type_val) return null;

            blk: {
                l_elem_ty = l_elem_ty.pointerElementType(analyser, .one) orelse break :blk;
                r_elem_ty = r_elem_ty.pointerElementType(analyser, .one) orelse break :blk;
                l_elem_ty = try l_elem_ty.instanceUnchecked(analyser);
                r_elem_ty = try r_elem_ty.instanceUnchecked(analyser);
                var elem_ty = try analyser.resolveArrayCat(l_elem_ty, r_elem_ty) orelse return null;
                elem_ty = try elem_ty.typeOf(analyser);
                const pointer_ty = try Type.createPointerType(analyser, .one, .none, true, elem_ty);
                return try pointer_ty.instanceUnchecked(analyser);
            }

            return try analyser.resolveArrayCat(l_elem_ty, r_elem_ty);
        },

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
        .assign_destructure,
        => {},

        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        => {},

        .root,
        .test_decl,
        .@"errdefer",
        .@"defer",
        .switch_case_one,
        .switch_case_inline_one,
        .switch_case,
        .switch_case_inline,
        .switch_range,
        => {},
        .@"continue",
        .@"break",
        .@"return",
        => {
            return Type.fromIP(analyser, .noreturn_type, null);
        },

        .@"suspend",
        .@"resume",
        => {},

        .asm_simple,
        .@"asm",
        .asm_output,
        .asm_input,
        => {},

        .identifier,
        .address_of,
        .field_access,
        .slice,
        .slice_sentinel,
        .slice_open,
        .array_access,
        .deref,
        => {
            const binding = try analyser.resolveBindingOfNodeUncached(options) orelse return null;
            return binding.type;
        },
    }
    return null;
}

/// The declaration `hit` names, read under this frame's ACTUAL container
/// when that container is written inside the scope the name was found in.
///
/// The lexical walk decides WHICH declaration the name is; that answer is
/// never second-guessed here.  What this adds is the instantiation it is
/// read under, which is what turns a bare `T` or a bare `comptime n` into
/// the argument the caller actually passed.
///
/// Two shapes reach this, and only these two.  Either the container's scope
/// is inside the name's scope — the generic's own body, `value: T`.  Or the
/// name's scope is a DIRECT child of the container's scope — a member, so
/// `read` is written inside the struct `Box` returned and its own function
/// scope hangs directly off that struct's scope.  That second shape is the
/// one a one-directional walk missed.
///
/// The DIRECT parent is the whole point.  Anything merely nested beneath the
/// container — a block-local item, a nested fn, a callee nothing names —
/// is more than one level down and stays unframed, so it keeps answering
/// unknown.
///
/// Attaching cannot invent a binding either way.  Both substitutions
/// consulted later are keyed by the tokens THIS container binds, so a
/// declaration that mentions none of them is unaffected: a wider match
/// costs work, never a wrong answer.
fn withEnclosingContainer(options: ResolveOptions, hit: ScopedSymbol) Error!DeclWithHandle {
    const container = options.container_type orelse return hit.decl;
    if (hit.decl.container_type != null) return hit.decl;

    const scope_handle = switch (container.data) {
        .container => |info| info.scope_handle,
        else => return hit.decl,
    };
    if (scope_handle.handle.module != hit.decl.handle.module) return hit.decl;
    if (!scope_handle.handle.document.uri.eql(hit.decl.handle.document.uri)) return hit.decl;
    // A container whose scope IS the root is the whole file, and nothing
    // encloses the root — so a root-scoped container reaches every scope in
    // its own file.  That is where `fn invoke(context: anytype)` at file
    // scope lives: its container is the root, and the `context` it binds is
    // read out of `invoke`'s own function scope.
    // A container binds the declarations written INSIDE its scope, so the
    // question is whether the name's scope sits UNDER the container's.  A
    // METHOD of that container is the case the one-directional test got
    // backwards: `read` is written inside the struct the generic returned,
    // so `read`'s own function scope is a DESCENDANT of the container's
    // scope, and walking up from the container never reaches it.  The frame
    // was therefore dropped there, `@This()` fell back to
    // `innermostContainer`, and every bound entry came back as the bare
    // `type_parameter` placeholder — the key surviving with a value that no
    // longer names u64 or u8.
    //
    // Both directions are accepted: the enclosing direction this test
    // already allowed, and the descendant direction a method needs.  Neither
    // can invent a binding — the map consulted afterwards is this
    // container's own, keyed by the tokens this container binds.
    if (scope_handle.scope != .root and
        !try scopeEncloses(hit.decl.handle, hit.scope, scope_handle.scope))
    {
        // The container's scope is not inside the name's scope.  The one
        // remaining case is MEMBERSHIP: a member of the container is written
        // IN its scope, so a method's own function scope has the container's
        // scope as its DIRECT parent — `read` is declared inside the struct
        // `Box` returned, which is why walking up from the container never
        // reached it and the frame was dropped.
        //
        // Requiring the DIRECT parent is what separates a member from
        // anything merely nested beneath: a block-local item, a nested fn, or
        // a callee nothing names sits deeper than one level and stays
        // unframed, so it keeps answering unknown.
        const document_scope = try hit.decl.handle.getDocumentScope();
        const parent = document_scope.getScopeParent(hit.scope).unwrap() orelse
            return hit.decl;
        if (parent != scope_handle.scope) return hit.decl;
    }

    return .{
        .decl = hit.decl.decl,
        .handle = hit.decl.handle,
        .container_type = container,
    };
}

fn resolveBindingOfNodeUncached(analyser: *Analyser, options: ResolveOptions) Error!?Binding {
    const node_handle = options.node_handle;
    const node = node_handle.node;
    const handle = node_handle.handle;
    const tree = &handle.document.tree;

    switch (tree.nodeTag(node)) {
        .identifier => {
            const name_token = ast.identifierTokenFromIdentifierNode(tree, node) orelse return null;
            const name = offsets.identifierTokenToNameSlice(tree, name_token);

            const is_escaped_identifier = tree.source[tree.tokenStart(name_token)] == '@';
            if (!is_escaped_identifier) {
                if (std.mem.eql(u8, name, "_")) return null;
                if (try analyser.resolvePrimitive(name)) |primitive| {
                    return .{
                        .type = Type.fromIP(analyser, analyser.ip.typeOf(primitive), primitive),
                        .is_const = true,
                    };
                }
            }

            const hit = try analyser.lookupSymbolGlobalScoped(handle, name, tree.tokenStart(name_token)) orelse return null;
            const child = try withEnclosingContainer(options, hit);
            const child_ty = try child.resolveType(analyser) orelse return null;
            return .{
                .type = child_ty,
                .is_const = child.isConst(),
            };
        },

        .address_of => {
            const expr_node = tree.nodeData(node).node;

            const base_binding = try analyser.resolveBindingOfNodeInternal(options.at(expr_node)) orelse return null;

            return .{
                .type = try analyser.resolveAddressOf(base_binding.is_const, base_binding.type),
                .is_const = true,
            };
        },

        .field_access => {
            const lhs_node, const field_name = tree.nodeData(node_handle.node).node_and_token;

            const lhs = (try analyser.resolveBindingOfNodeInternal(options.at(lhs_node))) orelse return null;

            const symbol = offsets.identifierTokenToNameSlice(tree, field_name);

            return try analyser.resolveFieldAccessBinding(lhs, symbol);
        },

        .slice,
        .slice_sentinel,
        .slice_open,
        => {
            const slice = tree.fullSlice(node).?;

            const sliced = try analyser.resolveBindingOfNodeInternal(options.at(slice.ast.sliced)) orelse return null;

            const kind: BracketAccess = try .fromSlice(analyser, options, slice);

            return try analyser.resolveBracketAccess(sliced, kind);
        },

        .array_access => {
            const lhs_node, const rhs_node = tree.nodeData(node).node_and_node;

            const lhs = try analyser.resolveBindingOfNodeInternal(options.at(lhs_node)) orelse return null;

            const index = try analyser.resolveIntegerLiteral(u64, options.at(rhs_node));

            return try analyser.resolveBracketAccess(lhs, .{ .single = index });
        },

        .deref => {
            const expr_node = tree.nodeData(node).node;

            const base_type = try analyser.resolveTypeOfNodeInternal(options.at(expr_node)) orelse return null;

            return try analyser.resolveDerefBinding(base_type);
        },

        else => return .{
            .type = try analyser.resolveTypeOfNodeUncached(options) orelse return null,
            .is_const = true,
        },
    }
}

pub const ResolveOptions = struct {
    node_handle: NodeWithHandle,
    container_type: ?Type,

    /// `container_type` stays null: a question asked without a frame is a
    /// question about the declaration alone, which is the truth for every
    /// lookup that genuinely has no container in scope.
    pub fn of(node: Ast.Node.Index, handle: DocumentStore.Handle) ResolveOptions {
        return .{
            .node_handle = .of(node, handle),
            .container_type = null,
        };
    }

    /// One step DOWN inside the same frame: a different node, in the same
    /// declaration, read under the same actual container.
    ///
    /// This is the only way a resolution descends.  Reaching a child
    /// through it keeps the container context, which is what makes an
    /// identifier or a formal `anytype` mean what the enclosing frame says
    /// it means; dropping it answers the child as though no container were
    /// open.  It never changes the handle, so nothing here can carry one
    /// declaration's container into another declaration's body — a
    /// resolution that legitimately belongs to another declaration starts
    /// from that declaration's own `DeclWithHandle`, not from this frame.
    pub fn at(options: ResolveOptions, node: Ast.Node.Index) ResolveOptions {
        return .{
            .node_handle = .of(node, options.node_handle.handle),
            .container_type = options.container_type,
        };
    }
};

pub const Binding = struct {
    type: Type,
    is_const: bool,
};

/// Represents a resolved Zig type.
/// This is the return type of `resolveTypeOfNode`.
pub const Type = struct {
    data: Data,
    /// If true, the type `type`, the attached data is the value of the type value.
    /// ```zig
    /// const foo = u32; // is_type_val == true
    /// const bar = @as(u32, ...); // is_type_val == false
    /// ```
    /// if `data == .ip_index` then this field is equivalent to `data.ip_index.type == .type_type`
    is_type_val: bool,

    pub const Data = union(enum) {
        /// - `*const T`
        /// - `[*]T`
        /// - `[]const T`
        /// - `[*c]T`
        pointer: struct {
            size: std.builtin.Type.Pointer.Size,
            /// `.none` means no sentinel, `.unknown_unknown` means unknown sentinel
            sentinel: InternPool.Index,
            is_const: bool,
            elem_ty: *Type,
        },

        /// `[elem_count :sentinel]elem_ty`
        array: struct {
            elem_count: ?u64,
            /// `.none` means no sentinel, `.unknown_unknown` means unknown sentinel
            sentinel: InternPool.Index,
            elem_ty: *Type,
        },

        /// `.{a,b}`
        tuple: []Type,

        /// `?T`
        optional: *Type,

        /// `error_set!payload`
        error_union: struct {
            /// `null` if inferred error
            error_set: ?*Type,
            payload: *Type,
        },

        /// `Foo` in `Foo.bar` where `Foo = union(enum) { bar }`
        union_tag: *Type,

        /// - `struct {}`
        /// - `enum {}`
        /// - `union {}`
        /// - `opaque {}`
        container: Container,

        /// - Function: `fn () Foo`, `fn foo() Foo`
        function: Function,

        /// - `@compileError("")`
        compile_error: NodeWithHandle,

        /// `T` in `fn Foo(comptime T: type) type`
        type_parameter: TokenWithHandle,

        /// `anytype` in `fn foo(bar: anytype) @TypeOf(bar)`
        anytype_parameter: struct {
            token_handle: TokenWithHandle,
            type_from_callsite_references: ?*Type,
        },

        /// Branching types
        either: []const EitherEntry,

        /// Primitive type: `u8`, `bool`, `type`, etc.
        /// Primitive value: `true`, `false`, `null`, `undefined`
        ip_index: struct {
            type: InternPool.Index,
            index: ?InternPool.Index,
        },

        pub const Container = struct {
            scope_handle: ScopeWithHandle,
            bound_params: TokenToTypeMap,
            /// ACTUAL comptime values a formal was given that have no `Type`
            /// representation — an enum tag's name, a string's bytes.
            /// Empty for every container built by anything but a call site.
            bound_values: BoundValueMap = .empty,

            pub fn root(handle: DocumentStore.Handle) Container {
                return .{
                    .scope_handle = .{ .handle = handle, .scope = .root },
                    .bound_params = .empty,
                };
            }
        };

        pub const Function = struct {
            fn_token: Ast.TokenIndex,
            handle: DocumentStore.Handle,

            container_type: *Type,
            doc_comments: ?[]const u8,
            name: ?[]const u8,
            parameters: []Parameter,
            has_varargs: bool,
            return_value: *Type,
        };

        pub const Parameter = struct {
            doc_comments: ?[]const u8,
            modifier: ?Modifier,
            name: ?[]const u8,
            name_token: ?Ast.TokenIndex,
            type: Type,

            pub const Modifier = enum {
                comptime_param,
                noalias_param,
            };
        };

        pub const EitherEntry = struct {
            /// the `is_type_val` property is inherited from the containing `Type`
            type_data: Data,
            descriptor: []const u8,
        };

        fn createPointer(
            analyser: *Analyser,
            size: std.builtin.Type.Pointer.Size,
            sentinel: InternPool.Index,
            is_const: bool,
            elem_ty: Type,
        ) !Data {
            std.debug.assert(elem_ty.is_type_val);
            blk: {
                const elem_type = elem_ty.ipIndex() orelse break :blk;
                const index = try analyser.ip.get(.{
                    .pointer_type = .{
                        .elem_type = elem_type,
                        .sentinel = try analyser.coerceIP(elem_type, sentinel) orelse break :blk,
                        .flags = .{
                            .size = size,
                            .is_const = is_const,
                        },
                    },
                });
                return .{ .ip_index = .{ .type = .type_type, .index = index } };
            }
            return .{
                .pointer = .{
                    .size = size,
                    .sentinel = sentinel,
                    .is_const = is_const,
                    .elem_ty = try analyser.allocType(elem_ty),
                },
            };
        }

        fn createArray(
            analyser: *Analyser,
            elem_count: ?u64,
            sentinel: InternPool.Index,
            elem_ty: Type,
        ) !Data {
            std.debug.assert(elem_ty.is_type_val);
            blk: {
                const len = elem_count orelse break :blk;
                const child = elem_ty.ipIndex() orelse break :blk;
                const index = try analyser.ip.get(.{
                    .array_type = .{
                        .len = len,
                        .child = child,
                        .sentinel = try analyser.coerceIP(child, sentinel) orelse break :blk,
                    },
                });
                return .{ .ip_index = .{ .type = .type_type, .index = index } };
            }
            return .{
                .array = .{
                    .elem_count = elem_count,
                    .sentinel = sentinel,
                    .elem_ty = try analyser.allocType(elem_ty),
                },
            };
        }

        fn createTuple(analyser: *Analyser, elem_tys: []Type) !Data {
            const tys = try analyser.gpa.alloc(InternPool.Index, elem_tys.len);
            defer analyser.gpa.free(tys);

            const vals = try analyser.gpa.alloc(InternPool.Index, elem_tys.len);
            defer analyser.gpa.free(vals);

            for (tys, vals, elem_tys) |*ty, *val, elem_ty| {
                ty.* = elem_ty.ipIndex() orelse break;
                val.* = .none;
            } else {
                const types = try analyser.ip.getIndexSlice(tys);
                const values = try analyser.ip.getIndexSlice(vals);
                const index = try analyser.ip.get(.{ .tuple_type = .{ .types = types, .values = values } });
                return .{ .ip_index = .{ .type = .type_type, .index = index } };
            }

            return .{ .tuple = elem_tys };
        }

        fn createOptional(analyser: *Analyser, child_ty: Type) !Data {
            std.debug.assert(child_ty.is_type_val);
            if (child_ty.ipIndex()) |payload_type| {
                const index = try analyser.ip.get(.{ .optional_type = .{ .payload_type = payload_type } });
                return .{ .ip_index = .{ .type = .type_type, .index = index } };
            }
            return .{ .optional = try analyser.allocType(child_ty) };
        }

        fn createErrorUnion(
            analyser: *Analyser,
            error_set: ?Type,
            payload: Type,
        ) !Data {
            std.debug.assert(error_set == null or error_set.?.is_type_val);
            std.debug.assert(payload.is_type_val);
            blk: {
                const error_set_type: InternPool.Index =
                    if (error_set) |e|
                        e.ipIndex() orelse break :blk
                    else
                        .none;
                const payload_type = payload.ipIndex() orelse break :blk;
                const index = try analyser.ip.get(.{
                    .error_union_type = .{
                        .error_set_type = error_set_type,
                        .payload_type = payload_type,
                    },
                });
                return .{ .ip_index = .{ .type = .type_type, .index = index } };
            }
            return .{
                .error_union = .{
                    .error_set = if (error_set) |e| try analyser.allocType(e) else null,
                    .payload = try analyser.allocType(payload),
                },
            };
        }

        pub fn hashWithHasher(data: Data, hasher: anytype) void {
            hasher.update(&.{@intFromEnum(data)});
            switch (data) {
                .pointer => |info| {
                    std.hash.autoHash(hasher, info.size);
                    std.hash.autoHash(hasher, info.sentinel);
                    std.hash.autoHash(hasher, info.is_const);
                    info.elem_ty.hashWithHasher(hasher);
                },
                .array => |info| {
                    std.hash.autoHash(hasher, info.elem_count);
                    std.hash.autoHash(hasher, info.sentinel);
                    info.elem_ty.hashWithHasher(hasher);
                },
                .tuple => |elem_ty_slice| {
                    for (elem_ty_slice) |elem_ty| {
                        elem_ty.hashWithHasher(hasher);
                    }
                },
                .optional, .union_tag => |t| t.hashWithHasher(hasher),
                .error_union => |info| {
                    if (info.error_set) |error_set| {
                        error_set.hashWithHasher(hasher);
                    }
                    info.payload.hashWithHasher(hasher);
                },
                .container => |info| {
                    info.scope_handle.hashWithHasher(hasher);

                    // Commutative, so this agrees with the UNORDERED
                    // comparison below whatever order either map was built
                    // in: every entry is hashed on its own and folded in,
                    // with the count alongside.  Sorting would allocate and
                    // copying would duplicate the maps; neither is needed to
                    // say "these hold the same entries".
                    var params_fold: u64 = 0;
                    for (info.bound_params.keys(), info.bound_params.values()) |token_handle, ty| {
                        var entry: std.hash.Wyhash = .init(0);
                        token_handle.hashWithHasher(&entry);
                        ty.hashWithHasher(&entry);
                        params_fold +%= entry.final();
                    }
                    std.hash.autoHash(hasher, info.bound_params.count());
                    std.hash.autoHash(hasher, params_fold);

                    var values_fold: u64 = 0;
                    for (info.bound_values.keys(), info.bound_values.values()) |token_handle, value| {
                        var entry: std.hash.Wyhash = .init(0);
                        token_handle.hashWithHasher(&entry);
                        value.hashWithHasher(&entry);
                        values_fold +%= entry.final();
                    }
                    std.hash.autoHash(hasher, info.bound_values.count());
                    std.hash.autoHash(hasher, values_fold);
                },
                .function => |info| {
                    std.hash.autoHash(hasher, info.fn_token);
                    std.hash.autoHash(hasher, info.handle.module);
                    hasher.update(info.handle.document.uri.raw);
                    info.container_type.hashWithHasher(hasher);
                    for (info.parameters) |param| {
                        param.type.hashWithHasher(hasher);
                    }
                    info.return_value.hashWithHasher(hasher);
                },
                .compile_error => |node_handle| {
                    std.hash.autoHash(hasher, node_handle.node);
                    std.hash.autoHash(hasher, node_handle.handle.module);
                    hasher.update(node_handle.handle.document.uri.raw);
                },
                .type_parameter => |token_handle| token_handle.hashWithHasher(hasher),
                .anytype_parameter => |info| {
                    info.token_handle.hashWithHasher(hasher);
                    if (info.type_from_callsite_references) |t| {
                        t.hashWithHasher(hasher);
                    }
                },
                .either => |entries| {
                    for (entries) |entry| {
                        hasher.update(entry.descriptor);
                        entry.type_data.hashWithHasher(hasher);
                    }
                },
                .ip_index => |payload| {
                    std.hash.autoHash(hasher, payload.type);
                    std.hash.autoHash(hasher, payload.index);
                },
            }
        }

        pub fn eql(a: Data, b: Data) bool {
            if (@intFromEnum(a) != @intFromEnum(b)) return false;

            switch (a) {
                .pointer => |a_type| {
                    const b_type = b.pointer;
                    if (a_type.size != b_type.size) return false;
                    if (a_type.sentinel != b_type.sentinel) return false;
                    if (!a_type.elem_ty.eql(b_type.elem_ty.*)) return false;
                },
                .array => |a_type| {
                    const b_type = b.array;
                    if (!std.meta.eql(a_type.elem_count, b_type.elem_count)) return false;
                    if (a_type.sentinel != b_type.sentinel) return false;
                    if (!a_type.elem_ty.eql(b_type.elem_ty.*)) return false;
                },
                .tuple => |a_slice| {
                    const b_slice = b.tuple;
                    if (a_slice.len != b_slice.len) return false;
                    for (a_slice, b_slice) |a_type, b_type| {
                        if (!a_type.eql(b_type)) return false;
                    }
                },
                inline .optional,
                .union_tag,
                => |a_type, name| {
                    const b_type = @field(b, @tagName(name));
                    if (!a_type.eql(b_type.*)) return false;
                },
                .error_union => |info| {
                    const b_info = b.error_union;
                    if (!info.payload.eql(b_info.payload.*)) return false;
                    if ((info.error_set == null) != (b_info.error_set == null)) return false;
                    if (info.error_set) |a_error_set| {
                        if (!a_error_set.eql(b_info.error_set.?.*)) return false;
                    }
                },
                .container => |a_info| {
                    const b_info = b.container;
                    if (!a_info.scope_handle.eql(b_info.scope_handle)) return false;
                    if (a_info.bound_params.count() != b_info.bound_params.count()) return false;
                    for (a_info.bound_params.keys(), a_info.bound_params.values()) |a_token_handle, a_type| {
                        const b_type = b_info.bound_params.get(a_token_handle) orelse return false;
                        if (!a_type.eql(b_type)) return false;
                    }
                    if (a_info.bound_values.count() != b_info.bound_values.count()) return false;
                    for (a_info.bound_values.keys(), a_info.bound_values.values()) |a_token_handle, a_value| {
                        const b_value = b_info.bound_values.get(a_token_handle) orelse return false;
                        if (!a_value.eql(b_value)) return false;
                    }
                },
                .function => |a_info| {
                    const b_info = b.function;
                    if (a_info.fn_token != b_info.fn_token) return false;
                    if (a_info.handle.module != b_info.handle.module) return false;
                    if (!a_info.handle.document.uri.eql(b_info.handle.document.uri)) return false;
                    if (!a_info.container_type.eql(b_info.container_type.*)) return false;
                    if (a_info.parameters.len != b_info.parameters.len) return false;
                    for (a_info.parameters, b_info.parameters) |a_param, b_param| {
                        if (!a_param.type.eql(b_param.type)) return false;
                    }
                    if (!a_info.return_value.eql(b_info.return_value.*)) return false;
                },
                .compile_error => |a_node_handle| return a_node_handle.eql(b.compile_error),
                .type_parameter => |a_token_handle| return a_token_handle.eql(b.type_parameter),
                .anytype_parameter => |a_info| {
                    const b_info = b.anytype_parameter;
                    if (!a_info.token_handle.eql(b_info.token_handle)) return false;
                    const a_type_maybe = a_info.type_from_callsite_references;
                    const b_type_maybe = b_info.type_from_callsite_references;
                    if (a_type_maybe) |a_type| {
                        const b_type = b_type_maybe orelse return false;
                        if (!a_type.eql(b_type.*)) return false;
                    } else {
                        if (b_type_maybe != null) return false;
                    }
                },
                .either => |a_entries| {
                    const b_entries = b.either;

                    if (a_entries.len != b_entries.len) return false;
                    for (a_entries, b_entries) |a_entry, b_entry| {
                        if (!std.mem.eql(u8, a_entry.descriptor, b_entry.descriptor)) return false;
                        if (!a_entry.type_data.eql(b_entry.type_data)) return false;
                    }
                },
                .ip_index => |a_payload| {
                    const b_payload = b.ip_index;

                    if (a_payload.type != b_payload.type) return false;
                    if (a_payload.index != b_payload.index) return false;
                },
            }

            return true;
        }

        fn isGeneric(data: Data) bool {
            return switch (data) {
                .type_parameter => true,
                .anytype_parameter => true,
                .pointer => |info| info.elem_ty.data.isGeneric(),
                .array => |info| info.elem_ty.data.isGeneric(),
                .tuple => |types| {
                    for (types) |t| {
                        if (t.data.isGeneric()) {
                            return true;
                        }
                    }
                    return false;
                },
                .optional => |t| t.data.isGeneric(),
                .error_union => |info| {
                    if (info.payload.data.isGeneric()) {
                        return true;
                    }
                    if (info.error_set) |t| {
                        if (t.data.isGeneric()) { // is this possible?
                            return true;
                        }
                    }
                    return false;
                },
                .union_tag => |t| t.data.isGeneric(),
                // BOTH binding maps are semantic bindings, not just the
                // type ones.  A container whose entire identity is an
                // enum tag or a string binds NO type parameter at all, so
                // asking only about `bound_params` calls it non-generic —
                // and then `.function` is non-generic through it, and
                // `resolveGenericTypeInternal` returns the value untouched
                // instead of carrying the container through.  Two such
                // instantiations would then compare equal.
                .container => |info| info.bound_params.count() != 0 or info.bound_values.count() != 0,
                .function => |info| {
                    if (info.container_type.data.isGeneric()) {
                        return true;
                    }
                    if (info.return_value.data.isGeneric()) {
                        return true;
                    }
                    for (info.parameters) |param| {
                        if (param.type.data.isGeneric()) {
                            return true;
                        }
                    }
                    return false;
                },
                .either => |entries| {
                    for (entries) |entry| {
                        if (entry.type_data.isGeneric()) {
                            return true;
                        }
                    }
                    return false;
                },
                .compile_error,
                .ip_index,
                => false,
            };
        }

        const GenericSet = std.HashMapUnmanaged(Data, void, GenericContext, std.hash_map.default_max_load_percentage);

        const GenericContext = struct {
            bound_params: TokenToTypeMap,

            pub fn hash(ctx: GenericContext, data: Data) u64 {
                var hasher: std.hash.Wyhash = .init(0);
                data.hashWithHasher(&hasher);
                for (ctx.bound_params.keys(), ctx.bound_params.values()) |token_handle, ty| {
                    token_handle.hashWithHasher(&hasher);
                    ty.hashWithHasher(&hasher);
                }
                return hasher.final();
            }

            pub fn eql(ctx: GenericContext, a: Data, b: Data) bool {
                _ = ctx;
                return a.eql(b);
            }
        };

        fn resolveGeneric(
            data: Data,
            analyser: *Analyser,
            bound_params: TokenToTypeMap,
            visiting: *GenericSet,
        ) error{OutOfMemory}!Data {
            if (!data.isGeneric()) {
                return data;
            }
            const ctx: GenericContext = .{ .bound_params = bound_params };
            const gop = try visiting.getOrPutContext(analyser.gpa, data, ctx);
            if (gop.found_existing) return data;
            defer std.debug.assert(visiting.removeContext(data, ctx));
            switch (data) {
                .compile_error,
                .ip_index,
                => unreachable,
                .type_parameter => |token_handle| {
                    const t = bound_params.get(token_handle) orelse return data;
                    std.debug.assert(t.is_type_val);
                    return t.data.resolveGeneric(analyser, bound_params, visiting);
                },
                .anytype_parameter => |info| {
                    const t = bound_params.get(info.token_handle) orelse return data;
                    std.debug.assert(t.is_type_val);
                    return t.data.resolveGeneric(analyser, bound_params, visiting);
                },
                .pointer => |info| {
                    const size = info.size;
                    const sentinel = info.sentinel;
                    const is_const = info.is_const;
                    const elem_ty = try analyser.resolveGenericTypeInternal(info.elem_ty.*, bound_params, visiting);
                    return try createPointer(analyser, size, sentinel, is_const, elem_ty);
                },
                .array => |info| {
                    const elem_count = info.elem_count;
                    const sentinel = info.sentinel;
                    const elem_ty = try analyser.resolveGenericTypeInternal(info.elem_ty.*, bound_params, visiting);
                    return try createArray(analyser, elem_count, sentinel, elem_ty);
                },
                .tuple => |info| {
                    const elem_tys = blk: {
                        const types = try analyser.arena.alloc(Type, info.len);
                        for (info, types) |old, *new| {
                            new.* = try analyser.resolveGenericTypeInternal(old, bound_params, visiting);
                        }
                        break :blk types;
                    };
                    return try createTuple(analyser, elem_tys);
                },
                .optional => |info| {
                    const child_ty = try analyser.resolveGenericTypeInternal(info.*, bound_params, visiting);
                    return try createOptional(analyser, child_ty);
                },
                .error_union => |info| {
                    const error_set = if (info.error_set) |t| try analyser.resolveGenericTypeInternal(t.*, bound_params, visiting) else null;
                    const payload = try analyser.resolveGenericTypeInternal(info.payload.*, bound_params, visiting);
                    return try createErrorUnion(analyser, error_set, payload);
                },
                .union_tag => |info| return .{
                    .union_tag = try analyser.allocType(try analyser.resolveGenericTypeInternal(info.*, bound_params, visiting)),
                },
                .container => |info| return .{
                    .container = .{
                        .scope_handle = info.scope_handle,
                        .bound_params = blk: {
                            var new_params: TokenToTypeMap = .empty;
                            try new_params.ensureTotalCapacity(analyser.arena, info.bound_params.count());
                            for (info.bound_params.keys(), info.bound_params.values()) |k, v| {
                                const t = try analyser.resolveGenericTypeInternal(v, bound_params, visiting);
                                new_params.putAssumeCapacity(k, t);
                            }
                            break :blk new_params;
                        },
                        .bound_values = blk: {
                            var new_values: BoundValueMap = .empty;
                            try new_values.ensureTotalCapacity(analyser.arena, info.bound_values.count());
                            for (info.bound_values.keys(), info.bound_values.values()) |k, v| {
                                // The tag's NAME is the actual this call
                                // passed and is never substituted; the enum
                                // that tag belongs to is part of this
                                // substitution, so a tag whose enum is itself
                                // generic follows it.
                                new_values.putAssumeCapacity(k, switch (v) {
                                    .enum_tag => |tag| .{ .enum_tag = .{
                                        .name = tag.name,
                                        .enum_ty = try analyser.resolveGenericTypeInternal(
                                            tag.enum_ty,
                                            bound_params,
                                            visiting,
                                        ),
                                    } },
                                    .string => |bytes| .{ .string = bytes },
                                });
                            }
                            break :blk new_values;
                        },
                    },
                },
                .function => |info| return .{
                    .function = .{
                        .fn_token = info.fn_token,
                        .handle = info.handle,
                        .container_type = try analyser.allocType(try analyser.resolveGenericTypeInternal(info.container_type.*, bound_params, visiting)),
                        .doc_comments = info.doc_comments,
                        .name = info.name,
                        .parameters = blk: {
                            const parameters = try analyser.arena.alloc(Parameter, info.parameters.len);
                            for (info.parameters, parameters) |old, *new| {
                                new.* = .{
                                    .doc_comments = old.doc_comments,
                                    .modifier = old.modifier,
                                    .name = old.name,
                                    .name_token = old.name_token,
                                    .type = try analyser.resolveGenericTypeInternal(old.type, bound_params, visiting),
                                };
                            }
                            break :blk parameters;
                        },
                        .has_varargs = info.has_varargs,
                        .return_value = try analyser.allocType(try analyser.resolveGenericTypeInternal(info.return_value.*, bound_params, visiting)),
                    },
                },
                .either => |info| return .{
                    .either = blk: {
                        const entries = try analyser.arena.alloc(EitherEntry, info.len);
                        for (info, entries) |old, *new| {
                            new.* = .{
                                .type_data = try old.type_data.resolveGeneric(analyser, bound_params, visiting),
                                .descriptor = old.descriptor,
                            };
                        }
                        break :blk entries;
                    },
                },
            }
        }
    };

    pub const unknown_type: Type = .{
        .data = .{
            .ip_index = .{
                .type = .type_type,
                .index = null,
            },
        },
        .is_type_val = true,
    };

    fn createPointerType(
        analyser: *Analyser,
        size: std.builtin.Type.Pointer.Size,
        sentinel: InternPool.Index,
        is_const: bool,
        elem_ty: Type,
    ) !Type {
        return .{
            .data = try Data.createPointer(analyser, size, sentinel, is_const, elem_ty),
            .is_type_val = true,
        };
    }

    fn createArrayType(
        analyser: *Analyser,
        elem_count: ?u64,
        sentinel: InternPool.Index,
        elem_ty: Type,
    ) !Type {
        return .{
            .data = try Data.createArray(analyser, elem_count, sentinel, elem_ty),
            .is_type_val = true,
        };
    }

    fn createTupleType(analyser: *Analyser, elem_tys: []Type) !Type {
        return .{
            .data = try Data.createTuple(analyser, elem_tys),
            .is_type_val = true,
        };
    }

    fn createOptionalType(analyser: *Analyser, child_ty: Type) !Type {
        return .{
            .data = try Data.createOptional(analyser, child_ty),
            .is_type_val = true,
        };
    }

    fn createErrorUnionType(
        analyser: *Analyser,
        error_set: ?Type,
        payload: Type,
    ) !Type {
        return .{
            .data = try Data.createErrorUnion(analyser, error_set, payload),
            .is_type_val = true,
        };
    }

    pub fn hash32(self: Type) u32 {
        return @truncate(self.hash64());
    }

    pub fn hash64(self: Type) u64 {
        var hasher: std.hash.Wyhash = .init(0);
        self.hashWithHasher(&hasher);
        return hasher.final();
    }

    pub fn hashWithHasher(self: Type, hasher: anytype) void {
        hasher.update(&.{@intFromBool(self.is_type_val)});
        self.data.hashWithHasher(hasher);
    }

    pub fn eql(a: Type, b: Type) bool {
        if (a.is_type_val != b.is_type_val) return false;
        if (!a.data.eql(b.data)) return false;
        return true;
    }

    pub const ArraySet = ArrayMap(void);

    pub fn ArrayMap(comptime V: type) type {
        return std.array_hash_map.Custom(Type, V, ArrayMapContext, true);
    }

    pub const ArrayMapContext = struct {
        pub fn hash(self: ArrayMapContext, ty: Type) u32 {
            _ = self;
            return ty.hash32();
        }

        pub fn eql(self: ArrayMapContext, a: Type, b: Type, b_index: usize) bool {
            _ = self;
            _ = b_index;
            return a.eql(b);
        }
    };

    pub fn ipIndex(self: Type) ?InternPool.Index {
        return switch (self.data) {
            .ip_index => |payload| payload.index,
            else => null,
        };
    }

    fn withoutIPIndex(self: Type, analyser: *Analyser) Type {
        return switch (self.data) {
            .ip_index => |payload| fromIP(analyser, payload.type, null),
            else => self,
        };
    }

    pub fn fromIP(analyser: *Analyser, ty: InternPool.Index, index: ?InternPool.Index) Type {
        std.debug.assert(analyser.ip.isType(ty));
        if (index) |idx| std.debug.assert(analyser.ip.typeOf(idx) == ty);
        return .{
            .data = .{ .ip_index = .{ .type = ty, .index = index } },
            .is_type_val = ty == .type_type,
        };
    }

    pub const TypeWithDescriptor = struct {
        type: Type,
        descriptor: []const u8,
    };

    pub fn fromEither(analyser: *Analyser, entries: []const TypeWithDescriptor) error{OutOfMemory}!?Type {
        const arena = analyser.arena;
        if (entries.len == 0)
            return null;

        if (entries.len == 1)
            return entries[0].type;

        peer_type_resolution: {
            var chosen = entries[0].type;
            for (entries[1..]) |entry| {
                const candidate = entry.type;
                chosen = try analyser.resolvePeerTypes(chosen, candidate) orelse break :peer_type_resolution;
            }
            return chosen;
        }

        // Note that we don't hash/equate descriptors to remove
        // duplicates

        const DeduplicatorContext = struct {
            pub fn hash(self: @This(), item: Type.Data.EitherEntry) u32 {
                _ = self;
                const ty: Type = .{ .data = item.type_data, .is_type_val = true };
                return ty.hash32();
            }

            pub fn eql(self: @This(), a: Type.Data.EitherEntry, b: Type.Data.EitherEntry, b_index: usize) bool {
                _ = b_index;
                _ = self;
                const a_ty: Type = .{ .data = a.type_data, .is_type_val = true };
                const b_ty: Type = .{ .data = b.type_data, .is_type_val = true };
                return a_ty.eql(b_ty);
            }
        };
        const Deduplicator = std.array_hash_map.Custom(Type.Data.EitherEntry, void, DeduplicatorContext, true);

        var deduplicator: Deduplicator = .empty;
        defer deduplicator.deinit(arena);

        const has_type_val = for (entries) |entry| {
            if (entry.type.data == .compile_error) {
                continue;
            }
            break entry.type.is_type_val;
        } else entries[0].type.is_type_val;

        for (entries) |entry| {
            try deduplicator.put(
                arena,
                .{ .type_data = entry.type.data, .descriptor = entry.descriptor },
                {},
            );
            if (entry.type.data == .compile_error) {
                continue;
            }
            if (entry.type.is_type_val != has_type_val) {
                return null;
            }
        }

        if (deduplicator.count() == 1)
            return entries[0].type;

        return .{
            .data = .{ .either = try arena.dupe(Type.Data.EitherEntry, deduplicator.keys()) },
            .is_type_val = has_type_val,
        };
    }

    /// Resolves all possible types by recursively expanding any conditional types.
    /// Drops duplicates
    pub fn getAllTypesWithHandles(ty: Type, analyser: *Analyser) error{OutOfMemory}![]const Type {
        var all_types: ArraySet = .empty;
        _ = try ty.getAllTypesWithHandlesArraySet(analyser, &all_types);
        return all_types.keys();
    }

    fn isConditional(ty: Type) bool {
        return switch (ty.data) {
            .either => true,
            .anytype_parameter => true,
            .optional => |child_ty| child_ty.isConditional(),
            .pointer => |info| info.elem_ty.isConditional(),
            .array => |info| info.elem_ty.isConditional(),
            .tuple => |types| {
                for (types) |t|
                    if (t.isConditional()) return true;
                return false;
            },
            .container => |info| {
                for (info.bound_params.values()) |t|
                    if (t.isConditional()) return true;
                return false;
            },
            .error_union => |info| {
                if (info.payload.isConditional()) return true;
                if (info.error_set) |e|
                    if (e.isConditional()) return true;
                return false;
            },
            .function => |info| {
                if (info.container_type.isConditional()) return true;
                if (info.return_value.isConditional()) return true;
                for (info.parameters) |param|
                    if (param.type.isConditional()) return true;
                return false;
            },
            .union_tag,
            .compile_error,
            .type_parameter,
            .ip_index,
            => false,
        };
    }

    /// Returns true if we have reached the limit for analyzing combinations
    pub fn getAllTypesWithHandlesArraySet(ty: Type, analyser: *Analyser, all_types: *ArraySet) error{OutOfMemory}!bool {
        if (all_types.count() >= analyser.max_conditional_combos) {
            return true;
        }
        const arena = analyser.arena;
        if (!ty.isConditional()) {
            try all_types.put(arena, ty, {});
            return false;
        }
        switch (ty.data) {
            .union_tag,
            .compile_error,
            .type_parameter,
            .ip_index,
            => unreachable,
            .either => |entries| {
                for (entries) |entry| {
                    const entry_ty: Type = .{ .data = entry.type_data, .is_type_val = ty.is_type_val };
                    if (try entry_ty.getAllTypesWithHandlesArraySet(analyser, all_types)) {
                        return true;
                    }
                }
            },
            .anytype_parameter => |info| {
                if (info.type_from_callsite_references) |t| {
                    if (try t.getAllTypesWithHandlesArraySet(analyser, all_types)) {
                        return true;
                    }
                } else {
                    try all_types.put(arena, ty, {});
                }
            },
            .optional => |child_ty| {
                for (try child_ty.getAllTypesWithHandles(analyser)) |t| {
                    if (all_types.count() >= analyser.max_conditional_combos) {
                        return true;
                    }
                    const new_child_ty = try analyser.allocType(t);
                    try all_types.put(arena, .{ .data = .{ .optional = new_child_ty }, .is_type_val = ty.is_type_val }, {});
                }
            },
            inline .pointer, .array => |info, tag| {
                for (try info.elem_ty.getAllTypesWithHandles(analyser)) |t| {
                    if (all_types.count() >= analyser.max_conditional_combos) {
                        return true;
                    }
                    var new_info = info;
                    new_info.elem_ty = try analyser.allocType(t);
                    const data = @unionInit(Type.Data, @tagName(tag), new_info);
                    try all_types.put(arena, .{ .data = data, .is_type_val = ty.is_type_val }, {});
                }
            },
            .tuple => |types| {
                var possible_types: ArrayMap([]const Type) = .empty;
                for (types) |t| {
                    try possible_types.put(arena, t, try t.getAllTypesWithHandles(analyser));
                }
                var iter: ComboIterator = try .init(arena, &possible_types);
                while (iter.next()) |combo| {
                    if (all_types.count() >= analyser.max_conditional_combos) {
                        return true;
                    }
                    const new_types = try arena.alloc(Type, types.len);
                    for (new_types, types) |*new, old| new.* = combo.get(old).?;
                    try all_types.put(arena, .{ .data = .{ .tuple = new_types }, .is_type_val = ty.is_type_val }, {});
                }
            },
            .container => |info| {
                var possible_types: ArrayMap([]const Type) = .empty;
                const types = info.bound_params.values();
                for (types) |t| {
                    try possible_types.put(arena, t, try t.getAllTypesWithHandles(analyser));
                }
                var iter: ComboIterator = try .init(arena, &possible_types);
                while (iter.next()) |combo| {
                    if (all_types.count() >= analyser.max_conditional_combos) {
                        return true;
                    }
                    const new_types = try arena.alloc(Type, types.len);
                    for (new_types, types) |*new, old| new.* = combo.get(old).?;
                    var new_info = info;
                    new_info.bound_params = try .init(arena, info.bound_params.keys(), new_types);
                    try all_types.put(arena, .{ .data = .{ .container = new_info }, .is_type_val = ty.is_type_val }, {});
                }
            },
            .error_union => |info| {
                var possible_types: ArrayMap([]const Type) = .empty;
                try possible_types.put(arena, info.payload.*, try info.payload.getAllTypesWithHandles(analyser));
                if (info.error_set) |t| {
                    try possible_types.put(arena, t.*, try t.getAllTypesWithHandles(analyser));
                }
                var iter: ComboIterator = try .init(arena, &possible_types);
                while (iter.next()) |combo| {
                    if (all_types.count() >= analyser.max_conditional_combos) {
                        return true;
                    }
                    var new_info = info;
                    new_info.payload = try analyser.allocType(combo.get(info.payload.*).?);
                    if (info.error_set) |t| {
                        new_info.error_set = try analyser.allocType(combo.get(t.*).?);
                    }
                    try all_types.put(arena, .{ .data = .{ .error_union = new_info }, .is_type_val = ty.is_type_val }, {});
                }
            },
            .function => |info| {
                var possible_types: ArrayMap([]const Type) = .empty;
                try possible_types.put(arena, info.container_type.*, try info.container_type.getAllTypesWithHandles(analyser));
                for (info.parameters) |param| {
                    try possible_types.put(arena, param.type, try param.type.getAllTypesWithHandles(analyser));
                }
                if (info.return_value.is_type_val) {
                    try possible_types.put(arena, info.return_value.*, try info.return_value.getAllTypesWithHandles(analyser));
                } else {
                    const return_type = try info.return_value.typeOf(analyser);
                    try possible_types.put(arena, return_type, try return_type.getAllTypesWithHandles(analyser));
                }
                var iter: ComboIterator = try .init(arena, &possible_types);
                while (iter.next()) |combo| {
                    if (all_types.count() >= analyser.max_conditional_combos) {
                        return true;
                    }
                    var new_info = info;
                    new_info.container_type = try analyser.allocType(combo.get(info.container_type.*).?);
                    new_info.parameters = try arena.alloc(Data.Parameter, info.parameters.len);
                    @memcpy(new_info.parameters, info.parameters);
                    for (new_info.parameters, info.parameters) |*new, old| {
                        new.type = combo.get(old.type).?;
                    }
                    if (info.return_value.is_type_val) {
                        new_info.return_value = try analyser.allocType(combo.get(info.return_value.*).?);
                    } else {
                        const return_type = try info.return_value.typeOf(analyser);
                        const return_value = try combo.get(return_type).?.instanceUnchecked(analyser);
                        new_info.return_value = try analyser.allocType(return_value);
                    }
                    try all_types.put(arena, .{ .data = .{ .function = new_info }, .is_type_val = ty.is_type_val }, {});
                }
            },
        }
        return false;
    }

    const ComboIterator = struct {
        possible_types: *const ArrayMap([]const Type),
        current_combo: ArrayMap(Type),
        total_combos: usize,
        counter: usize,

        fn init(
            arena: std.mem.Allocator,
            possible_types: *const ArrayMap([]const Type),
        ) error{OutOfMemory}!ComboIterator {
            var current_combo: ArrayMap(Type) = .empty;
            try current_combo.entries.resize(arena, possible_types.count());
            @memcpy(current_combo.keys(), possible_types.keys());
            try current_combo.reIndex(arena);

            var total_combos: usize = 1;
            for (possible_types.values()) |types| {
                total_combos *= types.len;
            }

            return .{
                .possible_types = possible_types,
                .current_combo = current_combo,
                .total_combos = total_combos,
                .counter = 0,
            };
        }

        fn next(iter: *ComboIterator) ?*const ArrayMap(Type) {
            if (iter.counter == iter.total_combos) return null;
            var x = iter.counter;
            for (iter.current_combo.values(), iter.possible_types.values()) |*t, types| {
                t.* = types[x % types.len];
                x /= types.len;
            }
            iter.counter += 1;
            return &iter.current_combo;
        }
    };

    pub fn instanceTypeVal(self: Type, analyser: *Analyser) error{OutOfMemory}!?Type {
        if (!self.is_type_val) return null;
        return try self.instanceUnchecked(analyser);
    }

    pub fn instanceUnchecked(self: Type, analyser: *Analyser) error{OutOfMemory}!Type {
        std.debug.assert(self.is_type_val);
        return switch (self.data) {
            .ip_index => |payload| fromIP(analyser, payload.index orelse try analyser.ip.getUnknown(payload.type), null),
            .either => |old_entries| {
                const new_entries = try analyser.arena.alloc(Type.Data.EitherEntry, old_entries.len);
                for (old_entries, new_entries) |old, *new| {
                    const old_type: Type = .{ .data = old.type_data, .is_type_val = self.is_type_val };
                    const new_type = try old_type.instanceUnchecked(analyser);
                    new.* = .{
                        .type_data = new_type.data,
                        .descriptor = old.descriptor,
                    };
                }
                return .{
                    .data = .{ .either = new_entries },
                    .is_type_val = false,
                };
            },
            else => .{ .data = self.data, .is_type_val = false },
        };
    }

    pub fn typeOf(self: Type, analyser: *Analyser) error{OutOfMemory}!Type {
        if (self.is_type_val) {
            return fromIP(analyser, .type_type, .type_type);
        }

        if (self.data == .ip_index) {
            return fromIP(analyser, .type_type, self.data.ip_index.type);
        }

        if (self.data == .either) {
            const old_entries = self.data.either;
            const new_entries = try analyser.arena.alloc(Type.Data.EitherEntry, old_entries.len);
            for (old_entries, new_entries) |old, *new| {
                const old_type: Type = .{ .data = old.type_data, .is_type_val = self.is_type_val };
                const new_type = try old_type.typeOf(analyser);
                new.* = .{
                    .type_data = new_type.data,
                    .descriptor = old.descriptor,
                };
            }
            return .{
                .data = .{ .either = new_entries },
                .is_type_val = true,
            };
        }

        return .{
            .data = self.data,
            .is_type_val = true,
        };
    }

    fn isRoot(self: Type) bool {
        switch (self.data) {
            .container => |info| return info.scope_handle.scope == Scope.Index.root,
            else => return false,
        }
    }

    pub fn isGenericType(self: Type) bool {
        return self.data.isGeneric();
    }

    fn getContainerKind(self: Type) ?std.zig.Token.Tag {
        const scope_handle = switch (self.data) {
            .container => |info| info.scope_handle,
            else => return null,
        };
        if (scope_handle.scope == .root) return .keyword_struct;

        const node = scope_handle.toNode();

        const tree = scope_handle.handle.document.tree;
        return tree.tokenTag(tree.nodeMainToken(node));
    }

    fn isContainerKind(self: Type, container_kind_tok: std.zig.Token.Tag) bool {
        return self.getContainerKind() == container_kind_tok;
    }

    pub fn isStructType(self: Type, analyser: *Analyser) bool {
        if (!self.is_type_val) return false;
        return switch (self.data) {
            .tuple => true,
            .ip_index => |payload| {
                const index = payload.index orelse return false;
                return analyser.ip.zigTypeTag(index) == .@"struct";
            },
            else => self.isContainerKind(.keyword_struct) or self.isRoot(),
        };
    }

    pub fn isNamespace(self: Type) bool {
        const scope_handle = switch (self.data) {
            .tuple => |fields| return fields.len == 0,
            .container => |info| info.scope_handle,
            else => return false,
        };
        if (!self.isContainerKind(.keyword_struct)) return false;
        const node = scope_handle.toNode();
        const tree = &scope_handle.handle.document.tree;
        var buf: [2]Ast.Node.Index = undefined;
        const full = tree.fullContainerDecl(&buf, node) orelse return true;
        for (full.ast.members) |member| {
            if (tree.nodeTag(member).isContainerField()) return false;
        }
        return true;
    }

    pub fn isEnumType(self: Type) bool {
        return self.isContainerKind(.keyword_enum);
    }

    pub fn isUnionType(self: Type) bool {
        return self.isContainerKind(.keyword_union);
    }

    pub fn isOpaqueType(self: Type) bool {
        return self.isContainerKind(.keyword_opaque);
    }

    pub fn isTaggedUnion(self: Type) bool {
        return switch (self.data) {
            .container => |info| ast.isTaggedUnion(&info.scope_handle.handle.document.tree, info.scope_handle.toNode()),
            else => false,
        };
    }

    /// returns whether the given type is of type `type`.
    pub fn isMetaType(self: Type) bool {
        if (!self.is_type_val) return false;
        switch (self.data) {
            .ip_index => |payload| return payload.index == .type_type,
            else => return false,
        }
    }

    pub fn isErrorSetType(self: Type, analyser: *Analyser) bool {
        if (!self.is_type_val) return false;
        switch (self.data) {
            .ip_index => |payload| {
                const ip_index = payload.index orelse return false;
                return analyser.ip.zigTypeTag(ip_index) == .error_set;
            },
            else => return false,
        }
    }

    pub fn isEnumLiteral(self: Type) bool {
        switch (self.data) {
            .ip_index => |payload| return payload.type == .enum_literal_type,
            else => return false,
        }
    }

    pub fn resolveDeclLiteralResultType(ty: Type) Type {
        std.debug.assert(ty.is_type_val);
        var result_type = ty;
        while (true) {
            result_type = switch (result_type.data) {
                .optional => |child_ty| child_ty.*,
                .error_union => |info| info.payload.*,
                .pointer => |child_ty| child_ty.elem_ty.*,
                else => return result_type,
            };
        }
    }

    pub fn isTypeFunc(self: Type) bool {
        return switch (self.data) {
            .function => |info| info.return_value.is_type_val,
            else => false,
        };
    }

    /// Returns whether the given function has a `anytype` parameter.
    pub fn isGenericFunc(self: Type) bool {
        return switch (self.data) {
            .function => |info| {
                for (info.parameters) |param| {
                    if (param.type.data == .anytype_parameter or param.modifier == .comptime_param) {
                        return true;
                    }
                }
                return false;
            },
            else => false,
        };
    }

    pub fn isFunc(self: Type) bool {
        return switch (self.data) {
            .function => true,
            else => false,
        };
    }

    pub fn isNoreturnType(self: Type) bool {
        if (!self.is_type_val) return false;
        return switch (self.data) {
            .compile_error => true,
            .ip_index => |payload| payload.index == .noreturn_type,
            else => false,
        };
    }

    fn pointerSize(self: Type, analyser: *Analyser) ?std.builtin.Type.Pointer.Size {
        if (self.is_type_val) return null;
        return switch (self.data) {
            .pointer => |info| info.size,
            .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
                .pointer_type => |pointer_info| pointer_info.flags.size,
                else => null,
            },
            else => null,
        };
    }

    fn pointerElementType(
        self: Type,
        analyser: *Analyser,
        size: std.builtin.Type.Pointer.Size,
    ) ?Type {
        if (self.is_type_val) return null;
        return switch (self.data) {
            .pointer => |info| {
                if (info.size != size) return null;
                return info.elem_ty.*;
            },
            .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
                .pointer_type => |pointer_info| {
                    if (pointer_info.flags.size != size) return null;
                    return Type.fromIP(analyser, .type_type, pointer_info.elem_type);
                },
                else => null,
            },
            else => null,
        };
    }

    fn arrayInfo(ty: Type, analyser: *Analyser) ?struct { ?u64, InternPool.Index, Type } {
        if (ty.is_type_val) return null;
        return switch (ty.data) {
            .array => |info| .{
                info.elem_count,
                info.sentinel,
                info.elem_ty.*,
            },
            .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
                .array_type => |array_info| .{
                    array_info.len,
                    array_info.sentinel,
                    Type.fromIP(analyser, .type_type, array_info.child),
                },
                else => null,
            },
            else => null,
        };
    }

    pub fn typeDefinitionToken(self: Type) ?TokenWithHandle {
        return switch (self.data) {
            .container => |info| {
                const container = info.scope_handle.toNode();
                var buf: [2]Ast.Node.Index = undefined;
                const tree = &info.scope_handle.handle.document.tree;
                // try to parse something that looks like (and only looks like) `const X = @This();`
                if (tree.fullContainerDecl(&buf, container)) |container_decl| {
                    for (container_decl.ast.members) |decl| {
                        const full_decl = tree.fullVarDecl(decl) orelse continue;

                        const init_node = full_decl.ast.init_node.unwrap() orelse continue;
                        if (!ast.isBuiltinCall(tree, init_node)) continue;
                        const builtin_name = tree.nodeMainToken(init_node);
                        std.debug.assert(tree.tokenTag(builtin_name) == .builtin);
                        const builtin_name_text = tree.tokenSlice(builtin_name);
                        if (!std.mem.eql(u8, builtin_name_text, "@This")) continue;

                        return .{
                            .token = full_decl.ast.mut_token + 1,
                            .handle = info.scope_handle.handle,
                        };
                    }
                }

                return .{
                    .token = info.scope_handle.handle.document.tree.firstToken(info.scope_handle.toNode()),
                    .handle = info.scope_handle.handle,
                };
            },
            .function => |info| .{
                .token = info.fn_token,
                .handle = info.handle,
            },
            else => null,
        };
    }

    pub fn docComments(self: Type, allocator: std.mem.Allocator) error{OutOfMemory}!?[]const u8 {
        if (self.is_type_val) {
            switch (self.data) {
                .container => |info| return try getDocComments(allocator, &info.scope_handle.handle.document.tree, info.scope_handle.toNode()),
                .function => |info| return info.doc_comments,
                else => {},
            }
        }
        return null;
    }

    pub fn lookupSymbol(
        self: Type,
        analyser: *Analyser,
        symbol: []const u8,
    ) Error!?DeclWithHandle {
        switch (self.data) {
            .either => |entries| {
                // TODO: Return all options instead of first valid one
                for (entries) |entry| {
                    const entry_ty: Type = .{ .data = entry.type_data, .is_type_val = self.is_type_val };
                    if (try entry_ty.lookupSymbol(analyser, symbol)) |decl| {
                        return decl;
                    }
                }
                return null;
            },
            else => {},
        }
        if (self.is_type_val) {
            if (self.isEnumType() or self.isTaggedUnion()) {
                if (try lookupSymbolContainer(self, symbol, .field)) |decl| {
                    return decl;
                }
            }
            return try lookupSymbolContainer(self, symbol, .other);
        } else {
            if (try lookupSymbolContainer(self, symbol, .other)) |decl| {
                const ty = try decl.resolveType(analyser) orelse return null;
                const func_type = try analyser.resolveFuncProtoOfCallable(ty) orelse return null;
                if (analyser.firstParamIs(func_type, try self.typeOf(analyser))) {
                    return decl;
                }
            }
            if (self.isEnumType()) {
                return null;
            }
            return try lookupSymbolContainer(self, symbol, .field);
        }
    }

    pub fn stringifyTypeOf(ty: Type, analyser: *Analyser, options: FormatOptions) error{OutOfMemory}![]const u8 {
        const typeof = try ty.typeOf(analyser);
        var aw: std.Io.Writer.Allocating = .init(analyser.arena);
        defer aw.deinit();
        rawStringify(typeof, &aw.writer, analyser, options) catch |err| switch (err) {
            error.OutOfMemory, error.WriteFailed => return error.OutOfMemory,
        };
        return aw.toOwnedSlice();
    }

    pub fn stringifyTypeVal(ty: Type, analyser: *Analyser, options: FormatOptions) error{OutOfMemory}![]const u8 {
        std.debug.assert(ty.data == .ip_index or ty.is_type_val);
        var aw: std.Io.Writer.Allocating = .init(analyser.arena);
        defer aw.deinit();
        rawStringify(ty, &aw.writer, analyser, options) catch |err| switch (err) {
            error.OutOfMemory, error.WriteFailed => return error.OutOfMemory,
        };
        return aw.toOwnedSlice();
    }

    fn writeString(str: []const u8, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        try writer.writeAll(str);
    }

    pub const FormatOptions = struct {
        referenced: ?*ReferencedType.Set = null,
        truncate_container_decls: bool,
    };

    fn rawStringify(
        ty: Type,
        writer: *std.Io.Writer,
        analyser: *Analyser,
        options: FormatOptions,
    ) error{ OutOfMemory, WriteFailed }!void {
        const referenced = options.referenced;

        switch (ty.data) {
            .pointer => |info| {
                switch (info.size) {
                    .one => try writer.writeByte('*'),
                    .many => {
                        try writer.writeAll("[*");
                        if (info.sentinel != .none) {
                            try writer.writeByte(':');
                            if (info.sentinel != .unknown_unknown) {
                                try writer.print("{f}", .{info.sentinel.fmt(analyser.ip)});
                            } else {
                                try writer.writeByte('?');
                            }
                        }
                        try writer.writeByte(']');
                    },
                    .slice => {
                        try writer.writeAll("[");
                        if (info.sentinel != .none) {
                            try writer.writeByte(':');
                            if (info.sentinel != .unknown_unknown) {
                                try writer.print("{f}", .{info.sentinel.fmt(analyser.ip)});
                            } else {
                                try writer.writeByte('?');
                            }
                        }
                        try writer.writeByte(']');
                    },
                    .c => try writer.writeAll("[*c]"),
                }
                if (info.is_const) try writer.writeAll("const ");
                try info.elem_ty.rawStringify(writer, analyser, options);
            },
            .array => |info| {
                try writer.writeByte('[');
                if (info.elem_count) |count| {
                    try writer.print("{d}", .{count});
                } else {
                    try writer.writeAll("?");
                }
                if (info.sentinel != .none) {
                    try writer.writeByte(':');
                    if (info.sentinel != .unknown_unknown) {
                        try writer.print("{f}", .{info.sentinel.fmt(analyser.ip)});
                    } else {
                        try writer.writeByte('?');
                    }
                }
                try writer.writeByte(']');
                try info.elem_ty.rawStringify(writer, analyser, options);
            },
            .tuple => |elem_ty_slice| {
                try writer.writeAll("struct { ");
                for (elem_ty_slice, 0..) |elem_ty, i| {
                    if (i != 0) {
                        try writer.writeAll(", ");
                    }
                    try elem_ty.rawStringify(writer, analyser, options);
                }
                try writer.writeAll(" }");
            },
            .optional => |child_ty| {
                try writer.writeByte('?');
                try child_ty.rawStringify(writer, analyser, options);
            },
            .error_union => |info| {
                if (info.error_set) |error_set| {
                    try error_set.rawStringify(writer, analyser, options);
                }
                try writer.writeByte('!');
                try info.payload.rawStringify(writer, analyser, options);
            },
            .union_tag => |t| {
                try writer.writeAll("@typeInfo(");
                try t.rawStringify(writer, analyser, options);
                try writer.writeAll(").@\"union\".tag_type.?");
            },
            .container => |info| {
                const scope_handle = info.scope_handle;
                const handle = scope_handle.handle;
                const tree = &handle.document.tree;

                const node = scope_handle.toNode();

                switch (handle.document.tree.nodeTag(node)) {
                    .root => {
                        const path = handle.document.uri.toFsPath(analyser.arena) catch |err| switch (err) {
                            error.OutOfMemory => return error.OutOfMemory,
                            error.UnsupportedScheme => handle.document.uri.raw,
                        };
                        const str = std.Io.Dir.path.stem(path);
                        try writer.writeAll(str);
                        if (referenced) |r| try r.put(analyser.arena, .of(str, handle, tree.firstToken(node)), {});
                    },

                    .container_decl,
                    .container_decl_arg,
                    .container_decl_arg_trailing,
                    .container_decl_trailing,
                    .container_decl_two,
                    .container_decl_two_trailing,
                    .tagged_union,
                    .tagged_union_trailing,
                    .tagged_union_two,
                    .tagged_union_two_trailing,
                    .tagged_union_enum_tag,
                    .tagged_union_enum_tag_trailing,
                    => {
                        // This is a hacky nightmare but it works :P
                        const token = tree.firstToken(node);
                        // `Foo = struct`
                        if (token >= 2 and tree.tokenTag(token - 2) == .identifier and tree.tokenTag(token - 1) == .equal) {
                            var str_token = token - 2;
                            // `Foo: type = struct`
                            if (token >= 4 and tree.tokenTag(token - 4) == .identifier and tree.tokenTag(token - 3) == .colon) {
                                str_token = token - 4;
                            }
                            const str = tree.tokenSlice(str_token);
                            try writer.writeAll(str);
                            if (referenced) |r| try r.put(analyser.arena, .of(str, handle, str_token), {});
                            return;
                        }
                        if (token >= 1 and tree.tokenTag(token - 1) == .keyword_return) blk: {
                            const doc_scope = try handle.getDocumentScope();
                            const function_scope = innermostScopeAtIndexWithTag(doc_scope, tree.tokenStart(token - 1), .initOne(.function)).unwrap() orelse break :blk;
                            const function_node = doc_scope.getScopeAstNode(function_scope).?;
                            var buf: [1]Ast.Node.Index = undefined;
                            const func = tree.fullFnProto(&buf, function_node).?;
                            const func_name_token = func.name_token orelse break :blk;
                            const func_name = offsets.tokenToSlice(tree, func_name_token);
                            try writer.writeAll(func_name);
                            if (referenced) |r| try r.put(analyser.arena, .of(func_name, handle, func_name_token), {});
                            var first = true;
                            try writer.writeByte('(');
                            var it: ast.FnParamIterator = .init(&func, tree);
                            while (it.next()) |param| {
                                const param_type_expr = param.type_expr orelse continue;
                                if (!Analyser.isMetaType(tree, param_type_expr)) continue;
                                const param_name_token = param.name_token orelse continue;
                                if (!first) {
                                    try writer.writeByte(',');
                                }
                                const param_ty = try analyser.resolveGenericType(.{
                                    .data = .{ .type_parameter = .{ .token = param_name_token, .handle = handle } },
                                    .is_type_val = true,
                                }, info.bound_params);

                                try param_ty.rawStringify(writer, analyser, .{
                                    .referenced = referenced,
                                    .truncate_container_decls = options.truncate_container_decls,
                                });
                                first = false;
                            }
                            try writer.writeByte(')');
                            return;
                        }

                        if (!options.truncate_container_decls) {
                            try writer.writeAll(offsets.nodeToSlice(tree, node));
                            return;
                        }

                        var container_decl_buffer: [2]Ast.Node.Index = undefined;
                        const container_decl = tree.fullContainerDecl(&container_decl_buffer, node).?;

                        const start_token = container_decl.layout_token orelse container_decl.ast.main_token;
                        const end_token = if (container_decl.ast.arg.unwrap()) |arg|
                            @min(ast.lastToken(tree, arg) + 1, tree.tokens.len)
                        else if (container_decl.ast.enum_token) |enum_token|
                            @min(enum_token + 1, tree.tokens.len)
                        else
                            container_decl.ast.main_token;

                        try writer.writeAll(offsets.tokensToSlice(tree, start_token, end_token));
                        if (container_decl.ast.members.len == 0) {
                            try writer.writeAll(" {}");
                        } else {
                            try writer.writeAll(" {...}");
                        }
                    },

                    else => unreachable,
                }
            },
            .function => |info| {
                try analyser.rawStringifyFunction(writer, .{
                    .referenced = referenced,
                    .info = info,
                    .include_fn_keyword = true,
                    .include_name = false,
                    .skip_first_param = false,
                    .parameters = .{ .show = .{
                        .include_modifiers = true,
                        .include_names = false,
                        .include_types = true,
                    } },
                    .include_return_type = true,
                    .snippet_placeholders = false,
                });
            },
            .ip_index => |payload| {
                const ip_index = payload.index orelse try analyser.ip.getUnknown(payload.type);
                try analyser.ip.print(ip_index, writer, .{
                    .truncate_container = options.truncate_container_decls,
                });
            },
            .either => try writer.writeAll("either type"), // TODO
            .compile_error => |node_handle| {
                if (options.truncate_container_decls) {
                    try writer.writeAll("@compileError(...)");
                } else {
                    try writer.writeAll(offsets.nodeToSlice(&node_handle.handle.document.tree, node_handle.node));
                }
            },
            .type_parameter => |token_handle| {
                const token = token_handle.token;
                const handle = token_handle.handle;
                const str = handle.document.tree.tokenSlice(token);
                try writer.writeAll(str);
                if (referenced) |r| try r.put(analyser.arena, .of(str, handle, token), {});
            },
            .anytype_parameter => |info| {
                const token = info.token_handle.token;
                const handle = info.token_handle.handle;
                const str = handle.document.tree.tokenSlice(token);
                std.debug.assert(std.mem.eql(u8, str, "anytype"));
                try writer.writeAll("anytype");
            },
        }
    }
};

pub const ScopeWithHandle = struct {
    handle: DocumentStore.Handle,
    scope: Scope.Index,

    pub fn toNode(scope_handle: ScopeWithHandle) Ast.Node.Index {
        if (scope_handle.scope == Scope.Index.root) return .root;
        var doc_scope = scope_handle.handle.document.document_scope.getCached();
        return doc_scope.getScopeAstNode(scope_handle.scope).?;
    }

    pub fn hashWithHasher(scope_handle: ScopeWithHandle, hasher: anytype) void {
        hasher.update(scope_handle.handle.document.uri.raw);
        std.hash.autoHash(hasher, scope_handle.handle.module);
        std.hash.autoHash(hasher, scope_handle.scope);
    }

    pub fn eql(a: ScopeWithHandle, b: ScopeWithHandle) bool {
        if (a.scope != b.scope) return false;
        if (a.handle.module != b.handle.module) return false;
        if (!a.handle.document.uri.eql(b.handle.document.uri)) return false;
        return true;
    }
};

pub fn resolveImportString(analyser: *Analyser, handle: DocumentStore.Handle, import_string: []const u8) Error!?Type {
    const result = try analyser.store.uriFromImportStr(analyser.arena, handle, import_string);
    switch (result) {
        .none => return null,
        .one => |target| {
            // The target carries the module it is read in, so the same file
            // entered from two modules yields two different root types.
            const target_handle = analyser.store.getOrLoadHandle(target.uri, target.module) catch |err| switch (err) {
                error.FileNotFound, error.NotDir => return null,
                error.Canceled => return error.Canceled,
                error.OutOfMemory => return error.OutOfMemory,
                error.SourceExcluded => return error.SourceExcluded,
            } orelse return null;
            return .{
                .data = .{ .container = .root(target_handle) },
                .is_type_val = true,
            };
        },
        .many => |targets| {
            var entries: std.ArrayList(Type.Data.EitherEntry) = try .initCapacity(analyser.arena, targets.len);
            for (targets) |target| {
                const target_handle = analyser.store.getOrLoadHandle(target.uri, target.module) catch |err| switch (err) {
                    error.FileNotFound, error.NotDir => continue,
                    error.Canceled => return error.Canceled,
                    error.OutOfMemory => return error.OutOfMemory,
                    error.SourceExcluded => return error.SourceExcluded,
                } orelse continue;
                entries.appendAssumeCapacity(.{
                    .type_data = .{ .container = .root(target_handle) },
                    .descriptor = "",
                });
            }
            return .{
                .data = .{ .either = entries.items },
                .is_type_val = true,
            };
        },
    }
}

fn resolveLangrefType(analyser: *Analyser, type_str: []const u8) Error!?Type {
    if (try analyser.resolvePrimitive(type_str)) |primitive|
        return Type.fromIP(analyser, primitive, null);

    // e.g. `?type`
    if (std.mem.startsWith(u8, type_str, "?")) {
        const elem_str = type_str[1..];
        const elem_instance = try analyser.resolveLangrefType(elem_str) orelse return null;
        const elem_ty = try elem_instance.typeOf(analyser);
        const optional_ty = try Type.createOptionalType(analyser, elem_ty);
        return try optional_ty.instanceUnchecked(analyser);
    }

    // e.g. `*const anyopaque`
    if (std.mem.startsWith(u8, type_str, "*")) {
        var elem_str = type_str[1..];
        const is_const = std.mem.startsWith(u8, elem_str, "const ");
        if (is_const)
            elem_str = elem_str[6..];
        const elem_instance = try analyser.resolveLangrefType(elem_str) orelse return null;
        const elem_ty = try elem_instance.typeOf(analyser);
        const pointer_ty = try Type.createPointerType(analyser, .one, .none, is_const, elem_ty);
        return try pointer_ty.instanceUnchecked(analyser);
    }

    // e.g. `[]const u8`
    if (std.mem.startsWith(u8, type_str, "[")) {
        const bracket_idx = std.mem.findScalar(u8, type_str, ']') orelse return null;

        var is_slice = bracket_idx == 1;
        var sentinel: InternPool.Index = .none;

        // e.g. `[:0]const u8`
        if (std.mem.findScalarLast(u8, type_str[0..bracket_idx], ':')) |colon_idx| {
            is_slice = colon_idx == 1;
            const sentinel_str = type_str[colon_idx + 1 .. bracket_idx];
            if (std.mem.eql(u8, sentinel_str, "0"))
                sentinel = .zero_comptime_int
            else
                sentinel = .unknown_unknown;
        }

        // e.g. `[N:0]u8`
        if (!is_slice) {
            const elem_str = type_str[bracket_idx + 1 ..];
            const elem_instance = try analyser.resolveLangrefType(elem_str) orelse return null;
            const elem_ty = try elem_instance.typeOf(analyser);
            const array_ty = try Type.createArrayType(analyser, null, sentinel, elem_ty);
            return try array_ty.instanceUnchecked(analyser);
        }

        var elem_str = type_str[bracket_idx + 1 ..];
        const is_const = std.mem.startsWith(u8, elem_str, "const ");
        if (is_const)
            elem_str = elem_str[6..];
        const elem_instance = try analyser.resolveLangrefType(elem_str) orelse return null;
        const elem_ty = try elem_instance.typeOf(analyser);
        const slice_ty = try Type.createPointerType(analyser, .slice, sentinel, is_const, elem_ty);
        return try slice_ty.instanceUnchecked(analyser);
    }

    return analyser.instanceStdBuiltinType(type_str);
}

/// Look up `type_name` in `zig_lib_dir/std/builtin.zig` as an instance.
/// Resolves builtin `AddressSpace`, `CallingConvention`, `Type`, and `assembly`.
pub fn instanceStdBuiltinType(analyser: *Analyser, type_name: []const u8) Error!?Type {
    const zig_lib_dir = analyser.store.config.zig_lib_dir orelse return null;
    const builtin_path = try zig_lib_dir.join(analyser.arena, &.{ "std", "builtin.zig" });
    const builtin_uri: Uri = try .fromPath(analyser.arena, builtin_path);

    // The toolchain is one proven environment of its own, so `builtin` is
    // not resolved in whichever module happened to ask for it first.
    const builtin_handle = analyser.store.getOrLoadHandle(builtin_uri, try analyser.store.toolchainModule()) catch |err| switch (err) {
        error.FileNotFound, error.NotDir => return null,
        error.Canceled => return error.Canceled,
        error.OutOfMemory => return error.OutOfMemory,
        error.SourceExcluded => return error.SourceExcluded,
    } orelse return null;
    const builtin_root_struct_type: Type = .{
        .data = .{ .container = .root(builtin_handle) },
        .is_type_val = true,
    };

    var result_ty = builtin_root_struct_type;
    var i: usize = 0;
    while (i < type_name.len) {
        const end = std.mem.findScalarPos(u8, type_name, i, '.') orelse type_name.len;
        const name = type_name[i..end];
        i = 1 + end;
        const decl = try result_ty.lookupSymbol(analyser, name) orelse return null;
        result_ty = try decl.resolveType(analyser) orelse return null;
    }
    return try result_ty.instanceTypeVal(analyser);
}

/// A resolved node, identified by the file it is in, the module that
/// file is read in, *and* the generic instantiation resolving it.
///
/// The same node index in one file means different things in two
/// modules, so the module is part of the key rather than decoration.
/// The same node in one module ALSO means different things under two
/// instantiations of one generic declaration — `Sha2x32(iv224, 224)`
/// and `Sha2x32(iv256, 256)` read the very same `digest_bits`
/// declaration and get different values — so the instantiation is part
/// of the key too.  Without it, one extant's answer would be served
/// for both.
pub const NodeWithUri = struct {
    node: Ast.Node.Index,
    uri: Uri,
    module: DocumentStore.ModuleId,
    comptime_values: ?*const ComptimeValues = null,
    /// The ACTUAL container this node is being read under, when there is
    /// one.  A separate field from `comptime_values` because that scope
    /// exists only for containers that bind VALUES: a container whose
    /// arguments are all types binds no value scope at all, so two of its
    /// instantiations would otherwise share one key and the first answer
    /// would be served for both.
    container_type: ?Type = null,

    const Context = struct {
        pub fn hash(self: Context, item: NodeWithUri) u64 {
            _ = self;
            var hasher: std.hash.Wyhash = .init(0);
            std.hash.autoHash(&hasher, item.node);
            hasher.update(item.uri.raw);
            std.hash.autoHash(&hasher, item.module);
            std.hash.autoHash(&hasher, @intFromPtr(item.comptime_values));
            if (item.container_type) |ty| ty.hashWithHasher(&hasher);
            return hasher.final();
        }

        pub fn eql(self: Context, a: NodeWithUri, b: NodeWithUri) bool {
            _ = self;
            if (a.node != b.node) return false;
            if (a.module != b.module) return false;
            if (a.comptime_values != b.comptime_values) return false;
            if ((a.container_type == null) != (b.container_type == null)) return false;
            if (a.container_type) |ty| {
                if (!ty.eql(b.container_type.?)) return false;
            }
            return a.uri.eql(b.uri);
        }
    };
};

pub const NodeWithHandle = struct {
    node: Ast.Node.Index,
    handle: DocumentStore.Handle,

    pub fn of(node: Ast.Node.Index, handle: DocumentStore.Handle) NodeWithHandle {
        return .{ .node = node, .handle = handle };
    }

    pub fn eql(a: NodeWithHandle, b: NodeWithHandle) bool {
        if (a.node != b.node) return false;
        if (a.handle.module != b.handle.module) return false;
        return a.handle.document.uri.eql(b.handle.document.uri);
    }
};

pub fn getFieldAccessType(
    analyser: *Analyser,
    handle: DocumentStore.Handle,
    source_index: usize,
    loc: offsets.Loc,
) Error!?Type {
    const held_range = try analyser.arena.dupeSentinel(u8, offsets.locToSlice(handle.document.tree.source, loc), 0);
    var tokenizer: std.zig.Tokenizer = .init(held_range);
    var current_type: ?Type = null;

    var do_unwrap_error_payload = false; // .keyword_try seen, ie `(try foo())`

    while (true) {
        const tok = tokenizer.next();
        switch (tok.tag) {
            .eof => return current_type,
            .identifier => {
                const symbol_name = offsets.identifierIndexToSlice(tokenizer.buffer, tok.loc.start, .name);
                if (try analyser.lookupSymbolGlobal(
                    handle,
                    symbol_name,
                    source_index,
                )) |child| {
                    current_type = (try child.resolveType(analyser)) orelse return null;
                } else return null;
            },
            .period => {
                const after_period = tokenizer.next();
                switch (after_period.tag) {
                    .eof => {
                        // function labels cannot be dot accessed
                        if (current_type) |ct| {
                            if (ct.isFunc()) return null;
                            return ct;
                        } else {
                            return null;
                        }
                    },
                    .identifier => {
                        if (after_period.loc.end == tokenizer.buffer.len) {
                            return current_type;
                        }

                        const symbol = offsets.identifierIndexToSlice(tokenizer.buffer, after_period.loc.start, .name);

                        current_type = try analyser.resolveFieldAccess(current_type orelse return null, symbol) orelse return null;
                    },
                    .question_mark => {
                        if (after_period.loc.end == tokenizer.buffer.len) {
                            return current_type;
                        }

                        current_type = (try analyser.resolveOptionalUnwrap(current_type orelse return null)) orelse return null;
                    },
                    else => {
                        log.debug("Unrecognized token {} after period.", .{after_period.tag});
                        return null;
                    },
                }
            },
            .period_asterisk => {
                if (tok.loc.end == tokenizer.buffer.len) {
                    return current_type;
                }

                current_type = (try analyser.resolveDerefType(current_type orelse return null)) orelse return null;
            },
            .l_paren => {
                if (current_type == null) {
                    // Likely `(expr)`
                    // Look for the corresponding .r_paren to form a slice of the contents
                    var paren_count: usize = 1;
                    var next = tokenizer.next();
                    while (next.tag != .eof) : (next = tokenizer.next()) {
                        if (next.tag == .r_paren) {
                            paren_count -= 1;
                            if (paren_count == 0) break;
                        } else if (next.tag == .l_paren) {
                            paren_count += 1;
                        }
                    } else return null;
                    current_type = try getFieldAccessType(
                        analyser,
                        handle,
                        source_index,
                        .{
                            // tok.loc and next.loc are offsets within held_range,
                            // add to loc.start to get offsets within handle.document.tree.source
                            .start = loc.start + tok.loc.end,
                            .end = loc.start + next.loc.start,
                        },
                    ) orelse return null;
                    continue;
                }

                const ty = try analyser.resolveFuncProtoOfCallable(current_type.?) orelse return null;

                // Can't call a function type, we need a function type instance.
                if (current_type.?.is_type_val) return null;

                // TODO Actually bind params here when calling functions instead of just skipping args.
                current_type = try analyser.resolveReturnType(ty) orelse return null;

                if (do_unwrap_error_payload) {
                    if (try analyser.resolveUnwrapErrorUnionType(current_type.?, .payload)) |unwrapped| current_type = unwrapped;
                    do_unwrap_error_payload = false;
                }

                // Skip to the right paren
                var paren_count: usize = 1;
                var next = tokenizer.next();
                while (next.tag != .eof) : (next = tokenizer.next()) {
                    if (next.tag == .r_paren) {
                        paren_count -= 1;
                        if (paren_count == 0) break;
                    } else if (next.tag == .l_paren) {
                        paren_count += 1;
                    }
                } else return null;
            },
            .l_bracket => {
                var bracket_count: usize = 1;
                var kind: BracketAccess = .{ .single = null };

                while (true) {
                    const token = tokenizer.next();
                    switch (token.tag) {
                        .eof => return null,
                        .r_bracket => {
                            bracket_count -= 1;
                            if (bracket_count == 0) break;
                        },
                        .l_bracket => {
                            bracket_count += 1;
                        },
                        .ellipsis2 => {
                            if (bracket_count == 1) {
                                kind = .{ .open = .{ .start = null, .sentinel = .none } };
                            }
                        },
                        else => {
                            if (bracket_count == 1 and kind == .open) {
                                kind = .{ .range = .{ .bounds = null, .sentinel = .none } };
                            }
                        },
                    }
                } else unreachable;

                current_type = (try analyser.resolveBracketAccessType(current_type orelse return null, kind)) orelse return null;
            },
            .builtin => {
                const binfn_name = tokenizer.buffer[tok.loc.start..tok.loc.end];

                if (std.mem.eql(u8, binfn_name, "@import")) {
                    if (tokenizer.next().tag != .l_paren) return null;
                    const import_str_tok = tokenizer.next(); // should be the .string_literal
                    if (import_str_tok.tag != .string_literal) return null;
                    if (import_str_tok.loc.end - import_str_tok.loc.start < 2) return null;
                    const import_str = offsets.locToSlice(tokenizer.buffer, .{
                        .start = import_str_tok.loc.start + 1,
                        .end = import_str_tok.loc.end - 1,
                    });
                    current_type = try analyser.resolveImportString(handle, import_str) orelse return null;
                    _ = tokenizer.next(); // eat the .r_paren
                    continue; // Outermost `while`
                }

                if (std.mem.eql(u8, binfn_name, "@typeInfo")) {
                    current_type = try analyser.instanceStdBuiltinType("Type") orelse return null;
                    // Skip to the right paren
                    var paren_count: usize = 0;
                    var next = tokenizer.next();
                    while (next.tag != .eof) : (next = tokenizer.next()) {
                        if (next.tag == .r_paren) {
                            paren_count -= 1;
                            if (paren_count == 0) break;
                        } else if (next.tag == .l_paren) {
                            paren_count += 1;
                        }
                    } else return null;
                    continue; // Outermost `while`
                }

                log.debug("Unhandled builtin: {s}", .{offsets.locToSlice(tokenizer.buffer, tok.loc)});
                return null;
            },
            // only hit when `(try foo())` otherwise getPositionContext never includes the `try` keyword
            .keyword_try => do_unwrap_error_payload = true,
            .l_brace => {
                var brace_count: usize = 1;
                var next = tokenizer.next();
                while (next.tag != .eof) : (next = tokenizer.next()) {
                    if (next.tag == .r_brace) {
                        brace_count -= 1;
                        if (brace_count == 0) break;
                    } else if (next.tag == .l_brace) {
                        brace_count += 1;
                    }
                } else return null;
                if (current_type) |ct| {
                    if (ct.isStructType(analyser) or ct.isUnionType()) {
                        // struct initialization
                        current_type = try ct.instanceTypeVal(analyser);
                    }
                }
            },
            else => {
                log.debug("Unimplemented token: {}", .{tok.tag});
                return null;
            },
        }
    }

    return current_type;
}

pub const PositionContext = union(enum) {
    builtin: offsets.Loc,
    import_string_literal: offsets.Loc,
    embedfile_string_literal: offsets.Loc,
    string_literal: offsets.Loc,
    field_access: offsets.Loc,
    var_access: offsets.Loc,
    /// `break :blk`
    /// `continue :blk`
    label_access: offsets.Loc,
    /// - `blk: {`
    /// - `blk: for`
    /// - `blk: while`
    /// - `blk: switch`
    label_decl: offsets.Loc,
    test_doctest_name: offsets.Loc,
    enum_literal: offsets.Loc,
    number_literal: offsets.Loc,
    char_literal: offsets.Loc,
    /// XXX: Internal use only, currently points to the loc of the first l_paren
    parens_expr: offsets.Loc,
    keyword: Ast.TokenIndex,
    error_access: offsets.Loc,
    comment,
    other,
    empty,

    pub fn loc(self: PositionContext, tree: *const Ast) ?offsets.Loc {
        return switch (self) {
            .builtin,
            .import_string_literal,
            .embedfile_string_literal,
            .string_literal,
            .field_access,
            .var_access,
            .label_access,
            .label_decl,
            .test_doctest_name,
            .enum_literal,
            .number_literal,
            .char_literal,
            .parens_expr,
            => |l| return l,
            .keyword => |token_index| return offsets.tokenToLoc(tree, token_index),
            .error_access,
            .comment,
            .other,
            .empty,
            => return null,
        };
    }

    /// Asserts that `self` is one of the following:
    ///  - `.import_string_literal`
    ///  - `.embedfile_string_literal`
    ///  - `.string_literal`
    pub fn stringLiteralContentLoc(self: PositionContext, source: []const u8) offsets.Loc {
        var location = switch (self) {
            .import_string_literal,
            .embedfile_string_literal,
            .string_literal,
            => |l| l,
            else => unreachable,
        };

        const string_literal_slice = offsets.locToSlice(source, location);
        if (std.mem.startsWith(u8, string_literal_slice, "\"")) {
            location.start += 1;
            if (std.mem.endsWith(u8, string_literal_slice[1..], "\"")) {
                location.end -= 1;
            }
            location.end = std.mem.findAnyPos(u8, source, location.start, &.{ '\n', '"' }) orelse source.len;
        } else if (std.mem.startsWith(u8, string_literal_slice, "\\")) {
            location.start += 2;
            location.end = std.mem.findScalarPos(u8, source, location.start, '\n') orelse source.len;
        }
        return location;
    }
};

const Stack = struct {
    states: std.ArrayList(State),

    const State = struct {
        ctx: PositionContext,
        scope: State.Scope,

        const Scope = enum { parens, brackets, braces, global };

        /// Indicates whether the current context is an ErrorSet definition, ie `error{...}`
        pub fn isErrSetDef(self: *Stack.State) bool {
            return (self.scope == .braces and self.ctx == .error_access);
        }
    };

    pub fn initCapacity(allocator: std.mem.Allocator, capacity: usize) error{OutOfMemory}!Stack {
        std.debug.assert(capacity > 0); // See `peek`.
        return .{ .states = try .initCapacity(allocator, capacity) };
    }

    pub fn deinit(self: *Stack, allocator: std.mem.Allocator) void {
        self.states.deinit(allocator);
    }

    pub fn push(self: *Stack, allocator: std.mem.Allocator, state: *const State) error{OutOfMemory}!void {
        try self.states.append(allocator, state.*);
    }

    pub fn peek(self: *Stack) *Stack.State {
        if (self.states.items.len == 0) {
            self.states.appendAssumeCapacity(.{ .ctx = .empty, .scope = .global });
        }
        return &self.states.items[self.states.items.len - 1];
    }

    /// Pops the last state off the stack. Sets previous state's ctx to .empty if !scopes_match
    pub fn pop(
        self: *Stack,
        /// Indicate whether the current state's scope matches the one being closed
        scopes_match: bool,
    ) void {
        if (self.states.items.len != 0) self.states.items.len -= 1;
        if (!scopes_match) self.peek().ctx = .empty;
    }
};

fn tokenLocAppend(prev: offsets.Loc, token: std.zig.Token) offsets.Loc {
    return .{
        .start = prev.start,
        .end = token.loc.end,
    };
}

/// Given a byte index in a document (typically cursor offset), classify what kind of entity is at that index.
///
/// Classification is based on the lexical structure -- we fetch the line containing index, and look at the
/// sequence of tokens just before the cursor. Due to the nice way zig is designed (only line comments, etc)
/// lexing just a single line is always correct.
pub fn getPositionContext(
    allocator: std.mem.Allocator,
    tree: *const Ast,
    source_index: usize,
    /// Should we look beyond the `source_index`? `false` for completions, `true` otherwise (hover, goto, etc.)
    lookahead: bool,
) error{OutOfMemory}!PositionContext {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    var line_loc = if (lookahead) offsets.lineLocAtIndex(tree.source, source_index) else offsets.lineLocUntilIndex(tree.source, source_index);

    if (std.mem.startsWith(u8, std.mem.trimStart(u8, offsets.locToSlice(tree.source, line_loc), " \t"), "//")) return .comment;

    // Check if the (trimmed) line starts with a '.', ie a continuation
    while (line_loc.start > 0) {
        while (std.mem.startsWith(u8, std.mem.trimStart(u8, offsets.locToSlice(tree.source, line_loc), " \t\r"), ".")) {
            if (line_loc.start > 1) {
                line_loc.start -= 2; // jump over a (potential) preceding '\n'
            } else break;
            while (line_loc.start > 0) : (line_loc.start -= 1) {
                if (tree.source[line_loc.start] == '\n') {
                    line_loc.start += 1; // eat the `\n`
                    break;
                }
            } else break;
        }
        if (line_loc.start != 0 and std.mem.startsWith(u8, std.mem.trimStart(u8, offsets.locToSlice(tree.source, line_loc), " \t"), "//")) {
            const prev_line_loc = offsets.lineLocAtIndex(tree.source, line_loc.start - 1); // `- 1` => prev line's `\n`
            line_loc.start = prev_line_loc.start;
            continue;
        }
        break;
    }

    // Check if the previous line ends with a ',', ie a continuation - targets multiline ErrorSet definitions
    var lloc = line_loc;
    while (true) {
        while (lloc.start > 0) {
            if (tree.source[lloc.start] != '\n') lloc.start -= 1 else break;
        } else break;
        while (lloc.start > 0 and tree.source[lloc.start] == '\n') lloc.start -= 1;
        if (lloc.start == 0) break;
        lloc = offsets.lineLocAtIndex(tree.source, lloc.start);
        // Check if it's a comment first
        while (lloc.start > 0 and std.mem.startsWith(u8, std.mem.trimStart(u8, offsets.locToSlice(tree.source, lloc), " \t"), "//")) {
            const prev_line_loc = offsets.lineLocAtIndex(tree.source, lloc.start - 1); // `- 1` => prev line's `\n`
            lloc = prev_line_loc;
        }
        if (std.mem.endsWith(u8, std.mem.trimEnd(u8, offsets.locToSlice(tree.source, lloc), " \t\r\n"), ",")) continue;
        line_loc.start = lloc.start;
        break;
    }

    var stack: Stack = try .initCapacity(allocator, 8);
    defer stack.deinit(allocator);
    var should_do_lookahead = lookahead;

    var current_token = offsets.sourceIndexToTokenIndex(tree, line_loc.start).preferLeft();
    var previous_token_end = line_loc.start;

    while (true) : (current_token += 1) {
        var tok: std.zig.Token = .{
            .tag = tree.tokenTag(current_token),
            .loc = offsets.tokenToLoc(tree, current_token),
        };
        tok.loc.end = @min(tok.loc.end, line_loc.end);
        defer previous_token_end = tok.loc.end;

        // Single '@' do not return a builtin token so we check this on our own.
        if (tok.tag == .invalid and tree.source[tok.loc.start] == '@') {
            if (std.mem.startsWith(u8, tree.source[tok.loc.start..], "@\"")) {
                tok.tag = .identifier;
                tok.loc = .{ .start = tok.loc.start, .end = @min(line_loc.end, tree.tokenStart(current_token + 1)) };
            } else if (std.mem.startsWith(u8, tree.source[tok.loc.start..], "@")) {
                tok.tag = .builtin;
                tok.loc = .{ .start = tok.loc.start, .end = tok.loc.start + 1 };
            }
        }

        if (source_index < tok.loc.start) break;
        if (source_index == tok.loc.start) {
            // Tie-breaking, the cursor is exactly between two tokens, and
            // `tok` is the latter of the two.
            if (!should_do_lookahead) break;
            should_do_lookahead = false;
            const curr_ctx = stack.peek();
            switch (tok.tag) {
                .identifier,
                .builtin,
                .number_literal,
                .string_literal,
                .multiline_string_literal_line,
                => {},
                .period => switch (curr_ctx.ctx) {
                    .empty => {},
                    else => if (previous_token_end == tok.loc.start) break,
                },
                else => if (previous_token_end == tok.loc.start) break,
            }
        }

        switch (tok.tag) {
            .invalid => {
                const s = tree.source[tok.loc.start..tok.loc.end];
                const q = std.mem.find(u8, s, "\"") orelse return .other;
                if (s[q -| 1] == '@') {
                    tok.tag = .identifier;
                } else {
                    tok.tag = .string_literal;
                }
            },
            .eof => break,
            else => {},
        }

        const curr_ctx: *Stack.State = stack.peek();
        defer switch (stack.peek().ctx) {
            .field_access => |*loc| loc.* = tokenLocAppend(loc.*, tok),
            else => {},
        };
        const new_state: PositionContext = switch (tok.tag) {
            .multiline_string_literal_line => .{ .string_literal = tok.loc },
            .string_literal,
            => new_state: {
                const string_literal_slice = offsets.locToSlice(tree.source, tok.loc);
                var content_loc = tok.loc;

                if (std.mem.startsWith(u8, string_literal_slice, "\"")) {
                    content_loc.start += 1;
                    if (std.mem.endsWith(u8, string_literal_slice[1..], "\"")) {
                        content_loc.end -= 1;
                    }
                }

                var new_state: PositionContext = .{ .string_literal = tok.loc };
                if (source_index < content_loc.start or content_loc.end < source_index) break :new_state new_state;

                if (curr_ctx.scope == .parens and
                    stack.states.items.len >= 2)
                {
                    const perhaps_builtin = stack.states.items[stack.states.items.len - 2];

                    switch (perhaps_builtin.ctx) {
                        .builtin => |loc| {
                            const builtin_name = tree.source[loc.start..loc.end];
                            if (std.mem.eql(u8, builtin_name, "@import")) {
                                new_state = .{ .import_string_literal = tok.loc };
                            } else if (std.mem.eql(u8, builtin_name, "@embedFile")) {
                                new_state = .{ .embedfile_string_literal = tok.loc };
                            }
                        },
                        else => {},
                    }
                }
                break :new_state new_state;
            },
            .identifier => if (curr_ctx.isErrSetDef())
                continue // Intent is to skip everything between the `error{...}` braces
            else switch (curr_ctx.ctx) {
                .enum_literal => |loc| .{ .enum_literal = tokenLocAppend(loc, tok) },
                .field_access => |loc| .{ .field_access = tokenLocAppend(loc, tok) },
                .label_access => |loc| if (loc.start == loc.end)
                    .{ .label_access = tok.loc }
                else
                    .{ .var_access = tok.loc },
                .test_doctest_name => .{ .test_doctest_name = tok.loc },
                else => .{ .var_access = tok.loc },
            },
            .builtin => .{ .builtin = tok.loc },
            .period => switch (curr_ctx.ctx) {
                .empty, .label_access => .{ .enum_literal = tok.loc },
                .enum_literal => .empty,
                .keyword => |token_index| switch (tree.tokenTag(token_index)) {
                    .keyword_break => .{ .enum_literal = tok.loc },
                    else => .other,
                },
                .comment, .other, .error_access => curr_ctx.ctx,
                .test_doctest_name, .var_access, .field_access => |loc| .{ .field_access = tokenLocAppend(loc, tok) },
                else => .{ .field_access = tokenLocAppend(curr_ctx.ctx.loc(tree) orelse tok.loc, tok) },
            },
            .period_asterisk => .{ .field_access = tokenLocAppend(curr_ctx.ctx.loc(tree) orelse tok.loc, tok) },
            .question_mark => switch (curr_ctx.ctx) {
                .field_access => |loc| .{ .field_access = tokenLocAppend(loc, tok) },
                else => .empty,
            },
            .colon => switch (curr_ctx.ctx) {
                .keyword => |token_index| switch (tree.tokenTag(token_index)) {
                    .keyword_break,
                    .keyword_continue,
                    => .{ .label_access = .{ .start = tok.loc.end, .end = tok.loc.end } },
                    else => .empty,
                },
                else => .empty,
            },
            .l_paren => {
                if (curr_ctx.ctx == .empty) curr_ctx.ctx = .{ .parens_expr = tok.loc };
                const scope: Stack.State.Scope = if (curr_ctx.ctx == .keyword) switch (tree.tokenTag(curr_ctx.ctx.keyword)) {
                    .keyword_for,
                    .keyword_if,
                    .keyword_while,
                    => .global,
                    else => .parens,
                } else .parens;
                try stack.push(allocator, &.{ .ctx = .empty, .scope = scope });
                continue;
            },
            .r_paren => {
                stack.pop(curr_ctx.scope == .parens);
                continue;
            },
            .l_bracket => {
                try stack.push(allocator, &.{ .ctx = .empty, .scope = .brackets });
                continue;
            },
            .r_bracket => {
                stack.pop(curr_ctx.scope == .brackets);
                continue;
            },
            .l_brace => {
                try stack.push(allocator, &.{ .ctx = if (curr_ctx.ctx == .error_access) curr_ctx.ctx else .empty, .scope = .braces });
                continue;
            },
            .r_brace => {
                stack.pop(curr_ctx.scope == .braces);
                continue;
            },
            .keyword_error => .{ .error_access = tok.loc },
            .number_literal => {
                if (tok.loc.start <= source_index and tok.loc.end >= source_index) {
                    return .{ .number_literal = tok.loc };
                }
                continue;
            },
            .char_literal => {
                if (tok.loc.start <= source_index and tok.loc.end >= source_index) {
                    return .{ .char_literal = tok.loc };
                }
                continue;
            },
            .keyword_addrspace,
            .keyword_break,
            .keyword_callconv,
            .keyword_continue,
            .keyword_for,
            .keyword_if,
            .keyword_switch,
            .keyword_while,
            => |tag| new_state: {
                std.debug.assert(tree.tokenTag(current_token) == tag);
                break :new_state .{ .keyword = current_token };
            },
            .keyword_test => .{ .test_doctest_name = .{ .start = tok.loc.end, .end = tok.loc.end } },
            .container_doc_comment => .comment,
            .doc_comment => new_state: {
                if (!curr_ctx.isErrSetDef()) break :new_state .comment; // Intent is to skip everything between the `error{...}` braces
                continue;
            },
            .comma => new_state: {
                if (!curr_ctx.isErrSetDef()) break :new_state .empty; // Intent is to skip everything between the `error{...}` braces
                continue;
            },
            else => .empty,
        };
        curr_ctx.ctx = new_state;
    }

    if (stack.states.pop()) |state| {
        switch (state.ctx) {
            .parens_expr => |loc| return .{ .var_access = loc },
            .var_access => |loc| {
                if (tree.tokenTag(current_token) == .colon) {
                    switch (tree.tokenTag(current_token + 1)) {
                        .l_brace,
                        .keyword_for,
                        .keyword_while,
                        .keyword_switch,
                        => return .{ .label_decl = loc },
                        else => {},
                    }
                }
                return state.ctx;
            },
            else => return state.ctx,
        }
    }

    return .empty;
}

pub const TokenToTypeMap = std.array_hash_map.Custom(TokenWithHandle, Type, TokenWithHandle.Context, true);

/// One ACTUAL comptime value a generic formal was given, in the only form
/// this engine can carry it.
///
/// The intern pool keys `enum_type` but has NO key for a tag VALUE, and no
/// key for a string value at all, so neither can live in a `Type`.  A
/// container's `bound_values` is where they are kept instead: borrowed
/// bytes and types owned by the arena that produced them.
pub const BoundValue = union(enum) {
    /// The NAME of an enum tag, together with the enum it belongs to, so
    /// the same spelling in two enums stays two different values.
    enum_tag: struct {
        name: []const u8,
        enum_ty: Type,
    },
    /// The DECODED BYTES of a string literal, allocated by the analyser
    /// arena and never borrowed raw from the source, because a decoded
    /// escape is not a substring of the text it was written as.
    string: []const u8,

    pub fn hashWithHasher(self: BoundValue, hasher: anytype) void {
        std.hash.autoHash(hasher, @intFromEnum(std.meta.activeTag(self)));
        switch (self) {
            .enum_tag => |info| {
                info.enum_ty.hashWithHasher(hasher);
                hasher.update(info.name);
            },
            .string => |bytes| hasher.update(bytes),
        }
    }

    pub fn eql(a: BoundValue, b: BoundValue) bool {
        return switch (a) {
            .enum_tag => |a_info| switch (b) {
                .enum_tag => |b_info| a_info.enum_ty.eql(b_info.enum_ty) and
                    std.mem.eql(u8, a_info.name, b_info.name),
                .string => false,
            },
            .string => |a_bytes| switch (b) {
                .string => |b_bytes| std.mem.eql(u8, a_bytes, b_bytes),
                .enum_tag => false,
            },
        };
    }
};

/// Keyed by the formal's NAME token: that is how a declaration names the
/// parameter when it is read back, and it is the one key both the
/// instantiation and the reader agree on.
pub const BoundValueMap = std.array_hash_map.Custom(TokenWithHandle, BoundValue, TokenWithHandle.Context, true);

pub const TokenWithHandle = struct {
    token: Ast.TokenIndex,
    handle: DocumentStore.Handle,

    pub fn hashWithHasher(token_handle: TokenWithHandle, hasher: anytype) void {
        std.hash.autoHash(hasher, token_handle.token);
        std.hash.autoHash(hasher, token_handle.handle.module);
        hasher.update(token_handle.handle.document.uri.raw);
    }

    pub fn eql(a: TokenWithHandle, b: TokenWithHandle) bool {
        if (a.token != b.token) return false;
        if (a.handle.module != b.handle.module) return false;
        if (!a.handle.document.uri.eql(b.handle.document.uri)) return false;
        return true;
    }

    const Context = struct {
        pub fn hash(self: Context, token_handle: TokenWithHandle) u32 {
            _ = self;
            var hasher: std.hash.Wyhash = .init(0);
            token_handle.hashWithHasher(&hasher);
            return @truncate(hasher.final());
        }

        pub fn eql(self: Context, a: TokenWithHandle, b: TokenWithHandle, b_index: usize) bool {
            _ = self;
            _ = b_index;
            return a.eql(b);
        }
    };
};

pub const DeclWithHandle = struct {
    decl: Declaration,
    handle: DocumentStore.Handle,
    container_type: ?Type = null,

    pub fn eql(a: DeclWithHandle, b: DeclWithHandle) bool {
        // Same declaration index, same file, different module: two
        // declarations, because the build wired them differently.
        if (a.handle.module != b.handle.module) return false;
        return a.decl.eql(b.decl) and a.handle.document.uri.eql(b.handle.document.uri);
    }

    /// Returns a `.identifier` or `.builtin` token.
    pub fn nameToken(self: DeclWithHandle) Ast.TokenIndex {
        return self.decl.nameToken(&self.handle.document.tree);
    }

    pub fn definitionToken(self: DeclWithHandle, analyser: *Analyser, resolve_alias: bool) Error!TokenWithHandle {
        if (resolve_alias) {
            if (try analyser.resolveVarDeclAlias(self)) |result| {
                return result.definitionToken(analyser, resolve_alias);
            }
            if (try self.resolveType(analyser)) |resolved_type| {
                if (resolved_type.is_type_val) {
                    if (resolved_type.typeDefinitionToken()) |token| {
                        return token;
                    }
                }
            }
        }
        return .{ .token = self.nameToken(), .handle = self.handle };
    }

    pub fn typeDeclarationNode(self: DeclWithHandle) error{OutOfMemory}!?NodeWithHandle {
        const tree = &self.handle.document.tree;
        switch (self.decl) {
            .ast_node => |node| switch (tree.nodeTag(node)) {
                .global_var_decl,
                .local_var_decl,
                .simple_var_decl,
                .aligned_var_decl,
                => {
                    const var_decl = tree.fullVarDecl(node).?;
                    const type_node = var_decl.ast.type_node.unwrap() orelse return null;
                    return .of(type_node, self.handle);
                },
                .container_field_init,
                .container_field_align,
                .container_field,
                => {
                    const container_field = tree.fullContainerField(node).?;
                    const type_expr = container_field.ast.type_expr.unwrap() orelse return null;
                    return .of(type_expr, self.handle);
                },
                .fn_proto,
                .fn_proto_multi,
                .fn_proto_one,
                .fn_proto_simple,
                .fn_decl,
                => return null,
                else => unreachable,
            },
            .assign_destructure => |payload| {
                const var_decl = payload.getFullVarDecl(tree);
                const type_node = var_decl.ast.type_node.unwrap() orelse return null;
                return .of(type_node, self.handle);
            },
            .function_parameter => |payload| {
                const param = payload.get(tree).?;
                const type_expr = param.type_expr orelse return null;
                return .of(type_expr, self.handle);
            },
            .optional_payload,
            .error_union_payload,
            .error_union_error,
            .for_loop_payload,
            .switch_payload,
            .switch_inline_tag_payload,
            => return null, // the payloads can't have a type specifier

            .label,
            .error_token,
            => return null,
        }
    }

    pub fn isConst(self: DeclWithHandle) bool {
        const tree = &self.handle.document.tree;
        return switch (self.decl) {
            .ast_node => |node| switch (tree.nodeTag(node)) {
                .global_var_decl,
                .local_var_decl,
                .aligned_var_decl,
                .simple_var_decl,
                => {
                    const mut_token = tree.fullVarDecl(node).?.ast.mut_token;
                    switch (tree.tokenTag(mut_token)) {
                        .keyword_var => return false,
                        .keyword_const => return true,
                        else => unreachable,
                    }
                },
                .container_field,
                .container_field_init,
                .container_field_align,
                .fn_proto,
                .fn_proto_multi,
                .fn_proto_one,
                .fn_proto_simple,
                .fn_decl,
                => true,
                else => unreachable,
            },
            .assign_destructure => |payload| {
                const mut_token = payload.getFullVarDecl(tree).ast.mut_token;
                switch (tree.tokenTag(mut_token)) {
                    .keyword_var => return false,
                    .keyword_const => return true,
                    else => unreachable,
                }
            },
            // some payload may be capture by ref but the pointer value is constant
            .function_parameter,
            .optional_payload,
            .for_loop_payload,
            .error_union_payload,
            .error_union_error,
            .switch_payload,
            .switch_inline_tag_payload,
            .label,
            .error_token,
            => true,
        };
    }

    pub fn isCaptureByRef(self: DeclWithHandle) bool {
        const tree = &self.handle.document.tree;
        return switch (self.decl) {
            .ast_node,
            .function_parameter,
            .error_union_error,
            .assign_destructure,
            .label,
            .error_token,
            .switch_inline_tag_payload,
            => false,
            inline .optional_payload,
            .for_loop_payload,
            .error_union_payload,
            => |payload| tree.tokenTag(payload.identifier - 1) == .asterisk,
            .switch_payload => |payload| tree.tokenTag(payload.getCase(tree).payload_token.?) == .asterisk,
        };
    }

    pub fn docComments(self: DeclWithHandle, allocator: std.mem.Allocator) error{OutOfMemory}!?[]const u8 {
        const tree = &self.handle.document.tree;
        return switch (self.decl) {
            .ast_node => |node| try getDocComments(allocator, tree, node),
            .function_parameter => |pay| {
                const param = pay.get(tree).?;
                const doc_comments = param.first_doc_comment orelse return null;
                return try collectDocComments(allocator, tree, doc_comments, false);
            },
            .error_token => |token| try getDocCommentsBeforeToken(allocator, tree, token),
            else => null,
        };
    }

    pub fn isPublic(self: DeclWithHandle) bool {
        const tree = self.handle.document.tree;
        var buf: [1]Ast.Node.Index = undefined;
        return switch (self.decl) {
            .ast_node => |node| switch (tree.nodeTag(node)) {
                .global_var_decl,
                .local_var_decl,
                .simple_var_decl,
                .aligned_var_decl,
                => tree.fullVarDecl(node).?.visib_token != null,
                .fn_proto,
                .fn_proto_multi,
                .fn_proto_one,
                .fn_proto_simple,
                .fn_decl,
                => tree.fullFnProto(&buf, node).?.visib_token != null,
                .container_field,
                .container_field_init,
                .container_field_align,
                => true,
                else => unreachable,
            },
            else => true,
        };
    }

    pub fn isStatic(self: DeclWithHandle) error{OutOfMemory}!bool {
        const tree = &self.handle.document.tree;
        return switch (self.decl) {
            .ast_node => |node| switch (tree.nodeTag(node)) {
                .global_var_decl,
                .local_var_decl,
                .simple_var_decl,
                .aligned_var_decl,
                => blk: {
                    const document_scope = try self.handle.getDocumentScope();
                    const token_index = tree.nodeMainToken(node);
                    const source_index = tree.tokenStart(token_index);
                    const scope_index = Analyser.innermostScopeAtIndex(document_scope, source_index);
                    break :blk document_scope.getScopeTag(scope_index).isContainer();
                },
                .container_field,
                .container_field_init,
                .container_field_align,
                .fn_proto,
                .fn_proto_multi,
                .fn_proto_one,
                .fn_proto_simple,
                .fn_decl,
                => false,
                else => unreachable,
            },
            else => false,
        };
    }

    /// One step DOWN inside this declaration: a different node, in the
    /// same document, read under the same ACTUAL container.
    ///
    /// Every branch of `resolveType` descends this way.  A payload
    /// condition, a parameter's declared type, a field's initializer and a
    /// switch selector are all written in the declaration's own body, so
    /// they resolve in its frame — dropping `container_type` would read a
    /// generic body as though no container were open, which is how a
    /// formal or a payload silently lost its instantiation.
    pub fn at(self: DeclWithHandle, node: Ast.Node.Index) ResolveOptions {
        return .{
            .node_handle = .of(node, self.handle),
            .container_type = self.container_type,
        };
    }

    pub fn resolveType(self: DeclWithHandle, analyser: *Analyser) Error!?Type {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();

        // A declaration read out of an instantiated container resolves
        // with that instantiation's ACTUAL argument values in scope, so
        // `digest_bits` means 224 under `Sha2x32(iv224, 224)` and 256
        // under `Sha2x32(iv256, 256)`.  A container that binds none
        // leaves the scope exactly as it was.
        const outer_values = analyser.comptime_values;
        analyser.comptime_values = (try analyser.comptimeValuesOfContainer(self.container_type)) orelse outer_values;
        defer analyser.comptime_values = outer_values;

        const tree = &self.handle.document.tree;
        var resolved_ty = switch (self.decl) {
            .ast_node => |node| try analyser.resolveTypeOfNodeInternal(self.at(node)),
            .function_parameter => |pay| blk: {
                // the `get` function never fails on declarations from the DocumentScope but
                // there may be manually created Declarations with invalid parameter indices.
                const param = pay.get(tree) orelse return null;

                // The ACTUAL value this instantiation supplied.  Without
                // it the engine could only answer "a `comptime_int` with
                // no value", which is exactly what left every extent
                // derived from `digest_bits` unknown.
                if (analyser.comptime_values) |values| {
                    const param_token: TokenWithHandle = .{
                        .token = self.decl.nameToken(tree),
                        .handle = self.handle,
                    };
                    if (values.get(param_token)) |value_index| {
                        break :blk Type.fromIP(analyser, analyser.ip.typeOf(value_index), value_index);
                    }
                }

                // The ACTUAL binding this instantiation supplied, read
                // straight out of the container's own bindings — before
                // scanning every call site, which can only answer with the
                // UNION of all of them: a different question from "what did
                // THIS instantiation pass", and a strictly worse answer
                // when the binding is sitting right here.
                //
                // The formal's NAME comes first and its value is returned
                // VERBATIM.  That value already carries the flags the call
                // passed — a type argument stays a type value, an instance
                // stays an instance, a function stays a function — so this
                // engine never has to choose one.
                //
                // Only when the name binds nothing does the `anytype`
                // KEYWORD token get consulted, and that one holds the TYPE
                // for generic substitution.  An `anytype` formal holds a
                // value of that type, so it is instantiated back — the
                // single place a type becomes an instance here, and only
                // because that binding is known to be a type.
                if (self.container_type) |container| {
                    if (container.data == .container) {
                        const bound_params = container.data.container.bound_params;

                        if (bound_params.get(.{
                            .token = self.decl.nameToken(tree),
                            .handle = self.handle,
                        })) |actual| {
                            break :blk actual;
                        }

                        if (param.anytype_ellipsis3) |anytype_token| {
                            if (tree.tokenTag(anytype_token) == .keyword_anytype) {
                                if (bound_params.get(.{
                                    .token = anytype_token,
                                    .handle = self.handle,
                                })) |actual| {
                                    break :blk if (actual.is_type_val)
                                        try actual.instanceUnchecked(analyser)
                                    else
                                        actual;
                                }
                            }
                        }
                    }
                }

                // handle anytype
                const type_expr = param.type_expr orelse {
                    const anytype_token = param.anytype_ellipsis3 orelse return null;
                    if (tree.tokenTag(anytype_token) != .keyword_anytype) return null;
                    const ty = try analyser.resolveCallsiteReferences(self);
                    break :blk Type{
                        .data = .{
                            .anytype_parameter = .{
                                .token_handle = .{ .token = anytype_token, .handle = self.handle },
                                .type_from_callsite_references = if (ty) |t| try analyser.allocType(t) else null,
                            },
                        },
                        .is_type_val = false,
                    };
                };

                const param_type = try analyser.resolveTypeOfNodeInternal(self.at(type_expr)) orelse return null;

                if (param_type.isMetaType()) {
                    const name_token = self.decl.nameToken(tree);
                    break :blk Type{
                        .data = .{ .type_parameter = .{ .token = name_token, .handle = self.handle } },
                        .is_type_val = true,
                    };
                }

                break :blk try param_type.instanceTypeVal(analyser);
            },
            .optional_payload => |pay| blk: {
                const ty = (try analyser.resolveTypeOfNodeInternal(self.at(pay.condition))) orelse return null;
                break :blk try analyser.resolveOptionalUnwrap(ty);
            },
            .error_union_payload => |pay| try analyser.resolveUnwrapErrorUnionType(
                (try analyser.resolveTypeOfNodeInternal(self.at(pay.condition))) orelse return null,
                .payload,
            ),
            .error_union_error => |pay| try analyser.resolveUnwrapErrorUnionType(
                (try analyser.resolveTypeOfNodeInternal(self.at(pay.condition.unwrap() orelse return null))) orelse return null,
                .error_set,
            ),
            .for_loop_payload => |pay| blk: {
                if (tree.nodeTag(pay.condition) == .for_range) {
                    break :blk Type.fromIP(analyser, .usize_type, null);
                }
                break :blk try analyser.resolveBracketAccessType(
                    (try analyser.resolveTypeOfNodeInternal(self.at(pay.condition))) orelse return null,
                    .{ .single = null },
                );
            },
            .assign_destructure => |pay| blk: {
                const var_decl = pay.getFullVarDecl(tree);
                if (var_decl.ast.type_node.unwrap()) |type_node| {
                    if (try analyser.resolveTypeOfNode(self.at(type_node))) |ty|
                        break :blk try ty.instanceTypeVal(analyser);
                }

                const init_node = tree.nodeData(pay.node).extra_and_node[1];
                const node = try analyser.resolveTypeOfNode(self.at(init_node)) orelse return null;
                if (node.is_type_val) return null;
                break :blk switch (node.data) {
                    .array => |array_info| try array_info.elem_ty.instanceTypeVal(analyser),
                    .tuple => try analyser.resolveBracketAccessType(node, .{ .single = pay.index }),
                    .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
                        .vector_type => |vector_info| Type.fromIP(analyser, vector_info.child, null),
                        .array_type => |array_info| Type.fromIP(analyser, array_info.child, null),
                        .tuple_type => try analyser.resolveBracketAccessType(node, .{ .single = pay.index }),
                        else => null,
                    },
                    else => null,
                };
            },
            .label => |decl| try analyser.resolveTypeOfNodeInternal(self.at(decl.block)),
            .switch_payload,
            .switch_inline_tag_payload,
            => |payload| blk: {
                const cond = tree.nodeData(payload.node).node_and_extra[0];
                const case = payload.getCase(tree);

                const switch_expr_type: Type = (try analyser.resolveTypeOfNodeInternal(self.at(cond))) orelse return null;

                if (self.decl == .switch_inline_tag_payload) {
                    return try analyser.resolveUnionTag(try switch_expr_type.typeOf(analyser));
                }

                if (switch_expr_type.isEnumType()) break :blk switch_expr_type;
                if (!switch_expr_type.isUnionType()) return switch_expr_type;

                if (case.ast.values.len == 0) {
                    if (case.inline_token == null) {
                        return switch_expr_type;
                    }
                    // TODO either type
                    return null;
                }

                // TODO Peer type resolution, we just use the first resolvable item for now.
                for (case.ast.values) |case_value| {
                    if (tree.nodeTag(case_value) != .enum_literal) continue;
                    const name_token = tree.nodeMainToken(case_value);
                    const name = offsets.identifierTokenToNameSlice(tree, name_token);
                    const decl = try switch_expr_type.lookupSymbol(analyser, name) orelse continue;
                    break :blk (try decl.resolveType(analyser)) orelse continue;
                }

                return null;
            },
            .error_token => return null,
        } orelse return null;

        if (self.container_type) |container_ty| {
            switch (container_ty.data) {
                .container => |info| {
                    resolved_ty = try analyser.resolveGenericType(resolved_ty, info.bound_params);
                },
                else => {},
            }
        }

        if (!self.isCaptureByRef()) return resolved_ty;

        const elem_ty = try resolved_ty.typeOf(analyser);
        const pointer_ty = try Type.createPointerType(analyser, .one, .none, false, elem_ty);
        return try pointer_ty.instanceUnchecked(analyser);
    }
};

/// Collects all symbols/declarations that can be a accessed on the given container type.
pub fn collectDeclarationsOfContainer(
    analyser: *Analyser,
    /// A container type (i.e. `struct`, `union`, `enum`, `opaque`)
    container_type: Type,
    original_handle: DocumentStore.Handle,
    /// Whether or not the container type is a instance of its type.
    /// ```zig
    /// const NotInstance = struct{};
    /// const instance = @as(struct{}, ...);
    /// ```
    instance_access: bool,
    /// allocated with `analyser.arena`
    decl_collection: *std.ArrayList(DeclWithHandle),
) Analyser.Error!void {
    const info = switch (container_type.data) {
        .container => |info| info,
        .either => |entries| {
            for (entries) |entry| {
                const ty: Type = .{ .data = entry.type_data, .is_type_val = container_type.is_type_val };
                try analyser.collectDeclarationsOfContainer(ty, original_handle, instance_access, decl_collection);
            }
            return;
        },
        else => return,
    };
    const container_scope = info.scope_handle;
    const scope = container_scope.scope;
    const handle = container_scope.handle;

    const tree = &handle.document.tree;
    const document_scope = try handle.getDocumentScope();
    const container_node = container_scope.toNode();
    const main_token = tree.nodeMainToken(container_node);

    const is_enum = tree.tokenTag(main_token) == .keyword_enum;

    const scope_decls = document_scope.getScopeDeclarationsConst(scope);

    for (scope_decls) |decl_index| {
        const decl = document_scope.declarations.get(@intFromEnum(decl_index));
        const decl_with_handle: DeclWithHandle = .{ .decl = decl, .handle = handle, .container_type = container_type };
        if (handle != original_handle and !decl_with_handle.isPublic()) continue;

        switch (decl) {
            .ast_node => |node| switch (tree.nodeTag(node)) {
                .container_field_init,
                .container_field_align,
                .container_field,
                => {
                    if (is_enum) {
                        if (instance_access) continue;
                        const field_name = offsets.tokenToSlice(tree, tree.nodeMainToken(node));
                        if (std.mem.eql(u8, field_name, "_")) continue;
                    } else {
                        if (!instance_access) continue;
                    }
                },
                .fn_proto,
                .fn_proto_multi,
                .fn_proto_one,
                .fn_proto_simple,
                .fn_decl,
                .global_var_decl,
                .local_var_decl,
                .simple_var_decl,
                .aligned_var_decl,
                => {
                    if (instance_access) {
                        // allow declarations which evaluate to functions where
                        // the first parameter has the type of the container:
                        const alias_type = try decl_with_handle.resolveType(analyser) orelse continue;
                        const func_ty = try analyser.resolveFuncProtoOfCallable(alias_type) orelse continue;

                        if (!analyser.firstParamIs(func_ty, .{
                            .data = .{ .container = info },
                            .is_type_val = true,
                        })) continue;
                    }
                },
                else => unreachable,
            },
            .label => continue,
            else => {},
        }

        try decl_collection.append(analyser.arena, decl_with_handle);
    }
}

/// Collects all symbols/declarations that are accessible at the given source index.
pub fn collectAllSymbolsAtSourceIndex(
    analyser: *Analyser,
    /// a handle to a Document
    handle: DocumentStore.Handle,
    /// a byte-index into `handle.document.tree.source`
    source_index: usize,
    /// allocated with `analyser.arena`
    decl_collection: *std.ArrayList(DeclWithHandle),
) error{OutOfMemory}!void {
    std.debug.assert(source_index <= handle.document.tree.source.len);

    const document_scope = try handle.getDocumentScope();
    var scope_iterator = iterateEnclosingScopes(document_scope, source_index);
    while (scope_iterator.next().unwrap()) |scope_index| {
        const scope_decls = document_scope.getScopeDeclarationsConst(scope_index);
        for (scope_decls) |decl_index| {
            const decl = document_scope.declarations.get(@intFromEnum(decl_index));
            if (decl == .ast_node and handle.document.tree.nodeTag(decl.ast_node).isContainerField()) continue;
            if (decl == .label) continue;
            try decl_collection.append(analyser.arena, .{ .decl = decl, .handle = handle });
        }
    }
}

pub const EnclosingScopeIterator = struct {
    document_scope: *const DocumentScope,
    current_scope: Scope.OptionalIndex,
    source_index: usize,

    pub fn next(self: *EnclosingScopeIterator) Scope.OptionalIndex {
        const current_scope = self.current_scope.unwrap() orelse return .none;
        const scopes = self.document_scope.getScopeChildScopesConst(current_scope);
        const scope_locs = self.document_scope.scopes.items(.loc);
        const result = self.current_scope;

        const Context = struct {
            scope_locs: []const DocumentScope.Scope.SmallLoc,
            source_index: usize,

            fn compare(ctx: @This(), scope_index: Scope.Index) std.math.Order {
                const child_scope = ctx.scope_locs[@intFromEnum(scope_index)];
                if (ctx.source_index < child_scope.start) return .lt;
                if (child_scope.end < ctx.source_index) return .gt;
                return .eq;
            }
        };

        self.current_scope = if (std.sort.binarySearch(
            Scope.Index,
            scopes,
            Context{ .scope_locs = scope_locs, .source_index = self.source_index },
            Context.compare,
        )) |scope_index| scopes[scope_index].toOptional() else .none;

        return result;
    }
};

fn iterateEnclosingScopes(document_scope: *const DocumentScope, source_index: usize) EnclosingScopeIterator {
    return .{
        .document_scope = document_scope,
        .current_scope = .root,
        .source_index = source_index,
    };
}

pub fn iterateLabels(handle: DocumentStore.Handle, source_index: usize, comptime callback: anytype, context: anytype) error{OutOfMemory}!void {
    const document_scope = try handle.getDocumentScope();
    var scope_iterator = iterateEnclosingScopes(document_scope, source_index);
    while (scope_iterator.next().unwrap()) |scope_index| {
        for (document_scope.getScopeDeclarationsConst(scope_index)) |decl_index| {
            const decl = document_scope.declarations.get(@intFromEnum(decl_index));
            if (decl != .label) continue;
            try callback(context, .{ .decl = decl, .handle = handle });
        }
    }
}

pub fn innermostScopeAtIndex(
    document_scope: *const DocumentScope,
    source_index: usize,
) Scope.Index {
    return innermostScopeAtIndexWithTag(document_scope, source_index, .full).unwrap().?;
}

pub fn innermostScopeAtIndexWithTag(
    document_scope: *const DocumentScope,
    source_index: usize,
    tag_filter: std.EnumSet(Scope.Tag),
) Scope.OptionalIndex {
    var scope_iterator = iterateEnclosingScopes(document_scope, source_index);
    var scope_index: Scope.OptionalIndex = .none;
    while (scope_iterator.next().unwrap()) |inner_scope| {
        const scope_tag = document_scope.getScopeTag(inner_scope);
        if (!tag_filter.contains(scope_tag)) continue;
        scope_index = inner_scope.toOptional();
    }
    return scope_index;
}

pub fn innermostContainer(analyser: *Analyser, handle: DocumentStore.Handle, source_index: usize) error{OutOfMemory}!Type {
    const tree = &handle.document.tree;
    const document_scope = try handle.getDocumentScope();
    if (document_scope.scopes.len == 1) return .{
        .data = .{ .container = .root(handle) },
        .is_type_val = true,
    };

    var pending_meta_params: TokenToTypeMap = .empty;
    defer pending_meta_params.deinit(analyser.gpa);

    var current: DocumentScope.Scope.Index = .root;
    var meta_params: TokenToTypeMap = .empty;
    var scope_iterator = iterateEnclosingScopes(document_scope, source_index);
    while (scope_iterator.next().unwrap()) |scope_index| {
        switch (document_scope.getScopeTag(scope_index)) {
            .container => {
                current = scope_index;
                for (pending_meta_params.keys(), pending_meta_params.values()) |token_handle, ty| {
                    try meta_params.put(analyser.arena, token_handle, ty);
                }
                pending_meta_params.clearRetainingCapacity();
            },
            .function => {
                const function_node = document_scope.getScopeAstNode(scope_index).?;
                var buf: [1]Ast.Node.Index = undefined;
                const func = tree.fullFnProto(&buf, function_node).?;
                var it: ast.FnParamIterator = .init(&func, tree);
                while (it.next()) |param| {
                    const param_type_expr = param.type_expr orelse continue;
                    if (!Analyser.isMetaType(tree, param_type_expr)) continue;
                    const param_name_token = param.name_token orelse continue;
                    const token_handle: TokenWithHandle = .{ .token = param_name_token, .handle = handle };
                    const ty: Type = .{ .data = .{ .type_parameter = token_handle }, .is_type_val = true };
                    try pending_meta_params.put(analyser.gpa, token_handle, ty);
                }
            },
            else => {},
        }
    }
    return .{
        .data = .{
            .container = .{
                .scope_handle = .{
                    .handle = handle,
                    .scope = current,
                },
                .bound_params = meta_params,
            },
        },
        .is_type_val = true,
    };
}

pub fn lookupLabel(
    handle: DocumentStore.Handle,
    symbol: []const u8,
    source_index: usize,
) error{OutOfMemory}!?DeclWithHandle {
    const document_scope = try handle.getDocumentScope();
    var scope_iterator = iterateEnclosingScopes(document_scope, source_index);
    while (scope_iterator.next().unwrap()) |scope_index| {
        const decl_index = document_scope.getScopeDeclaration(.{
            .scope = scope_index,
            .name = symbol,
            .kind = .label,
        }).unwrap() orelse continue;
        const decl = document_scope.declarations.get(@intFromEnum(decl_index));

        std.debug.assert(decl == .label);

        return .{ .decl = decl, .handle = handle };
    }
    return null;
}

/// A name found by the lexical scope walk, together with the scope that
/// claimed it.
///
/// The scope is what says whether an enclosing container's context applies
/// to this declaration: a name claimed inside a container is that
/// container's own, while one claimed at file scope is not.
const ScopedSymbol = struct {
    decl: DeclWithHandle,
    scope: Scope.Index,
};

fn lookupSymbolGlobalScoped(
    _: *Analyser,
    handle: DocumentStore.Handle,
    symbol: []const u8,
    source_index: usize,
) error{OutOfMemory}!?ScopedSymbol {
    const tree = &handle.document.tree;
    const document_scope = try handle.getDocumentScope();
    var current_scope = innermostScopeAtIndex(document_scope, source_index);

    while (true) {
        if (document_scope.getScopeDeclaration(.{
            .scope = current_scope,
            .name = symbol,
            .kind = .field,
        }).unwrap()) |decl_index| {
            const decl = document_scope.declarations.get(@intFromEnum(decl_index));
            std.debug.assert(decl == .ast_node);

            var field = tree.fullContainerField(decl.ast_node).?;
            field.convertToNonTupleLike(tree);

            const field_name = offsets.tokenToLoc(tree, field.ast.main_token);
            if (field_name.start <= source_index and source_index <= field_name.end) {
                return .{ .decl = .{ .decl = decl, .handle = handle }, .scope = current_scope };
            }
        }

        if (document_scope.getScopeDeclaration(.{
            .scope = current_scope,
            .name = symbol,
            .kind = .other,
        }).unwrap()) |decl_index| {
            const decl = document_scope.declarations.get(@intFromEnum(decl_index));
            return .{ .decl = .{ .decl = decl, .handle = handle }, .scope = current_scope };
        }

        current_scope = document_scope.getScopeParent(current_scope).unwrap() orelse break;
    }

    return null;
}

pub fn lookupSymbolGlobal(
    analyser: *Analyser,
    handle: DocumentStore.Handle,
    symbol: []const u8,
    source_index: usize,
) error{OutOfMemory}!?DeclWithHandle {
    const hit = try analyser.lookupSymbolGlobalScoped(handle, symbol, source_index) orelse return null;
    return hit.decl;
}

/// Is `outer` the scope `inner` sits in, or one of the scopes enclosing it?
///
/// Walking from `inner` up to `outer` is what says "the scope that owns
/// this name is where that container was written".
///
/// A container from a different file or module has no lexical relationship
/// to this one at all, so callers compare the handles before asking.
fn scopeEncloses(
    handle: DocumentStore.Handle,
    outer: Scope.Index,
    inner: Scope.Index,
) Error!bool {
    const document_scope = try handle.getDocumentScope();
    var current = inner;
    while (true) {
        if (current == outer) return true;
        current = document_scope.getScopeParent(current).unwrap() orelse return false;
    }
}

pub fn lookupSymbolContainer(
    container_type: Type,
    symbol: []const u8,
    kind: DocumentScope.DeclarationLookup.Kind,
) error{OutOfMemory}!?DeclWithHandle {
    const info = switch (container_type.data) {
        .container => |info| info,
        else => return null,
    };
    const container_scope = info.scope_handle;
    const handle = container_scope.handle;
    const document_scope = try handle.getDocumentScope();

    if (document_scope.getScopeDeclaration(.{
        .scope = container_scope.scope,
        .name = symbol,
        .kind = kind,
    }).unwrap()) |decl_index| {
        const decl = document_scope.declarations.get(@intFromEnum(decl_index));
        return .{ .decl = decl, .handle = handle, .container_type = container_type };
    }

    return null;
}

/// Is `node` the callee of the call that encloses it?
///
/// A root enum literal names a declaration only when it is being CALLED.
/// In value position it is an enum tag or a decl literal, and both keep
/// the answer `lookupSymbolFieldInit` gives them.  The lineage runs
/// innermost-first, so the enclosing call is the very next node.
fn isCallCallee(tree: *const Ast, node: Ast.Node.Index, enclosing: []const Ast.Node.Index) bool {
    if (enclosing.len == 0) return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, enclosing[0]) orelse return false;
    return call.ast.fn_expr == node;
}

/// The declaration a root enum literal callee names in the container its
/// call site expects.
///
/// `expected` is the parameter type at that call, and it is the only
/// basis this lookup may use: it is the type Zig itself resolves the name
/// against, and the one `lookupSymbolFieldInit` already reads for this
/// position.  No name is looked up anywhere else, so a PEER expected type
/// — several candidate containers, any of which `lookupSymbol` will
/// answer from — is refused rather than resolved against whichever
/// candidate happens to declare the name first.
///
/// Only a CALLABLE declaration is this callee.  A field or a constant in
/// that position does not compile, which is a different answer from "this
/// could not be read"; the caller tells the two apart, and neither is
/// ever taken on the strength of the name alone.
fn lookupEnumLiteralCallee(
    analyser: *Analyser,
    expected: Type,
    name: []const u8,
) Error!?DeclWithHandle {
    if (expected.is_type_val) return null;
    if (expected.data == .either) return null;
    const container = try expected.typeOf(analyser);
    const decl = try container.lookupSymbol(analyser, name) orelse return null;
    const declared = try decl.resolveType(analyser) orelse return null;
    if (try analyser.resolveFuncProtoOfCallable(declared) == null) return null;
    return decl;
}

pub fn lookupSymbolFieldInit(
    analyser: *Analyser,
    options: ResolveOptions,
    field_name: []const u8,
    node: Ast.Node.Index,
    ancestors: []const Ast.Node.Index,
) Error!?struct { DeclWithHandle, ?Type } {
    const handle = options.node_handle.handle;
    var container_type = (try analyser.resolveExpressionType(
        options,
        node,
        ancestors,
    )) orelse return null;

    if (container_type.is_type_val) return null;

    const is_struct_init = switch (handle.document.tree.nodeTag(node)) {
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init,
        .struct_init_comma,
        => true,
        else => false,
    };

    container_type = try container_type.typeOf(analyser);
    container_type = container_type.resolveDeclLiteralResultType();
    container_type = try container_type.instanceUnchecked(analyser);
    if (is_struct_init) {
        const decl = try container_type.lookupSymbol(analyser, field_name) orelse return null;
        return .{ decl, null };
    }

    switch (container_type.data) {
        .union_tag => |t| {
            const decl = try t.lookupSymbol(analyser, field_name) orelse return null;
            return .{ decl, container_type };
        },
        else => {},
    }

    switch (container_type.getContainerKind() orelse return null) {
        .keyword_struct, .keyword_opaque => {},
        .keyword_enum => if (try (try container_type.typeOf(analyser)).lookupSymbol(analyser, field_name)) |decl| return .{ decl, null },
        .keyword_union => if (try container_type.lookupSymbol(analyser, field_name)) |decl| return .{ decl, null },
        else => return null,
    }

    // Assume we are doing decl literals
    const decl = try (try container_type.typeOf(analyser)).lookupSymbol(analyser, field_name) orelse return null;
    var resolved_type = try decl.resolveType(analyser) orelse return null;
    resolved_type = try analyser.resolveReturnType(resolved_type) orelse resolved_type;
    resolved_type = try resolved_type.typeOf(analyser);
    resolved_type = resolved_type.resolveDeclLiteralResultType();
    resolved_type = try resolved_type.instanceUnchecked(analyser);
    if (resolved_type.eql(container_type)) return .{ decl, null };
    return null;
}

/// The type this expression has in the position it was written, read in
/// `options`' frame.  An enum literal and a decl literal are both named
/// against their EXPECTED type, and that expected type is a declaration of
/// the enclosing container — which is the one thing a context-free lookup
/// cannot supply.
pub fn resolveExpressionType(
    analyser: *Analyser,
    options: ResolveOptions,
    node: Ast.Node.Index,
    ancestors: []const Ast.Node.Index,
) Error!?Type {
    return (try analyser.resolveExpressionTypeFromAncestors(
        options,
        node,
        ancestors,
    )) orelse (try analyser.resolveTypeOfNode(options.at(node)));
}

pub fn resolveExpressionTypeFromAncestors(
    analyser: *Analyser,
    options: ResolveOptions,
    node: Ast.Node.Index,
    ancestors: []const Ast.Node.Index,
) Error!?Type {
    if (ancestors.len == 0) return null;

    const handle = options.node_handle.handle;
    const tree = &handle.document.tree;

    switch (tree.nodeTag(ancestors[0])) {
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init,
        .struct_init_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&buffer, ancestors[0]).?;
            if (std.mem.findScalar(Ast.Node.Index, struct_init.ast.fields, node) != null) {
                const field_name_token = tree.firstToken(node) - 2;
                if (tree.tokenTag(field_name_token) != .identifier) return null;
                const field_name = offsets.identifierTokenToNameSlice(tree, field_name_token);
                if (try analyser.lookupSymbolFieldInit(options, field_name, ancestors[0], ancestors[1..])) |field| {
                    const decl, const type_maybe = field;
                    return type_maybe orelse try decl.resolveType(analyser);
                }
            }
        },
        .array_init_one,
        .array_init_one_comma,
        .array_init_dot_two,
        .array_init_dot_two_comma,
        .array_init_dot,
        .array_init_dot_comma,
        .array_init,
        .array_init_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const array_init = tree.fullArrayInit(&buffer, ancestors[0]).?;
            const element_index = std.mem.findScalar(Ast.Node.Index, array_init.ast.elements, node) orelse
                return null;

            if (try analyser.resolveExpressionType(
                options.at(ancestors[0]),
                ancestors[0],
                ancestors[1..],
            )) |array_type| {
                return (try analyser.resolveBracketAccessType(array_type, .{ .single = element_index }));
            }
        },
        .container_field_init,
        .container_field_align,
        .container_field,
        => {
            const container_field = tree.fullContainerField(ancestors[0]).?;
            if (node.toOptional() == container_field.ast.value_expr) {
                return try analyser.resolveTypeOfNode(options.at(ancestors[0]));
            }
        },
        .global_var_decl,
        .local_var_decl,
        .simple_var_decl,
        .aligned_var_decl,
        => {
            const var_decl = tree.fullVarDecl(ancestors[0]).?;
            if (node.toOptional() == var_decl.ast.init_node) {
                return try analyser.resolveTypeOfNode(options.at(ancestors[0]));
            }
            if (node.toOptional() == var_decl.ast.addrspace_node) {
                return analyser.instanceStdBuiltinType("AddressSpace");
            }
            if (node.toOptional() == var_decl.ast.section_node) {
                const ty = try analyser.ip.get(.{
                    .pointer_type = .{
                        .elem_type = .u8_type,
                        .sentinel = .none,
                        .flags = .{
                            .size = .slice,
                            .is_const = true,
                        },
                    },
                });
                return Type.fromIP(analyser, ty, null);
            }
        },
        .if_simple,
        .@"if",
        => {
            const if_node = ast.fullIf(tree, ancestors[0]).?;
            if (node == if_node.ast.then_expr or node.toOptional() == if_node.ast.else_expr) {
                return try analyser.resolveExpressionType(
                    options.at(ancestors[0]),
                    ancestors[0],
                    ancestors[1..],
                );
            }
        },
        .for_simple,
        .@"for",
        => {
            const for_node = ast.fullFor(tree, ancestors[0]).?;
            if (node.toOptional() == for_node.ast.else_expr) {
                return try analyser.resolveExpressionType(
                    options.at(ancestors[0]),
                    ancestors[0],
                    ancestors[1..],
                );
            }
        },
        .while_simple,
        .while_cont,
        .@"while",
        => {
            const while_node = ast.fullWhile(tree, ancestors[0]).?;
            if (node.toOptional() == while_node.ast.else_expr) {
                return try analyser.resolveExpressionType(
                    options.at(ancestors[0]),
                    ancestors[0],
                    ancestors[1..],
                );
            }
        },
        .switch_case_one,
        .switch_case_inline_one,
        .switch_case,
        .switch_case_inline,
        => {
            const switch_case = tree.fullSwitchCase(ancestors[0]).?;
            if (ancestors.len == 1) return null;

            const ancestor_switch = tree.fullSwitch(ancestors[1]) orelse return null;

            if (node == switch_case.ast.target_expr) {
                return try analyser.resolveExpressionType(
                    options.at(ancestors[1]),
                    ancestors[1],
                    ancestors[2..],
                );
            }

            for (switch_case.ast.values) |value| {
                if (node == value) {
                    return try analyser.resolveTypeOfNode(options.at(ancestor_switch.ast.condition));
                }
            }
        },
        .call,
        .call_comma,
        .call_one,
        .call_one_comma,
        => {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, ancestors[0]).?;

            if (call.ast.fn_expr == node) {
                return try analyser.resolveExpressionType(
                    options.at(ancestors[0]),
                    ancestors[0],
                    ancestors[1..],
                );
            }

            const arg_index = std.mem.findScalar(Ast.Node.Index, call.ast.params, node) orelse return null;

            var fn_type = if (tree.nodeTag(call.ast.fn_expr) == .enum_literal) blk: {
                const field_name = offsets.identifierTokenToNameSlice(tree, tree.nodeMainToken(call.ast.fn_expr));
                const decl, const type_maybe = try analyser.lookupSymbolFieldInit(options, field_name, call.ast.fn_expr, ancestors) orelse return null;
                const ty = type_maybe orelse try decl.resolveType(analyser) orelse return null;
                break :blk try analyser.resolveFuncProtoOfCallable(ty) orelse return null;
            } else blk: {
                const ty = try analyser.resolveTypeOfNode(options.at(call.ast.fn_expr)) orelse return null;
                break :blk try analyser.resolveFuncProtoOfCallable(ty) orelse return null;
            };
            if (fn_type.is_type_val) return null;

            // The callee expression is written in THIS frame, so it is read
            // in this frame: `options.at` keeps the handle and the container.
            const frame = options.at(call.ast.fn_expr);
            fn_type = try analyser.resolveFunctionTypeFromCall(frame, call, fn_type);
            const has_self_param = try analyser.isInstanceCall(frame, call, fn_type);
            const parameters = fn_type.data.function.parameters[@intFromBool(has_self_param)..];
            if (arg_index >= parameters.len) return null;
            const param_ty = parameters[arg_index].type;
            return try param_ty.instanceTypeVal(analyser);
        },
        .assign => {
            const lhs, const rhs = tree.nodeData(ancestors[0]).node_and_node;
            if (node == rhs) {
                return try analyser.resolveTypeOfNode(options.at(lhs));
            }
        },
        .ptr_type_aligned,
        .ptr_type_sentinel,
        .ptr_type,
        .ptr_type_bit_range,
        => {
            const ptr = tree.fullPtrType(ancestors[0]).?;
            if (node.toOptional() == ptr.ast.sentinel) {
                return analyser.resolveInstanceOfNode(options.at(ptr.ast.child_type));
            }
            if (node.toOptional() == ptr.ast.addrspace_node) {
                return analyser.instanceStdBuiltinType("AddressSpace");
            }
        },
        .array_type_sentinel => {
            const array_type = tree.fullArrayType(ancestors[0]).?;
            if (node.toOptional() == array_type.ast.sentinel) {
                return analyser.resolveInstanceOfNode(options.at(array_type.ast.elem_type));
            }
        },

        .equal_equal, .bang_equal => {
            const lhs, const rhs = tree.nodeData(ancestors[0]).node_and_node;
            if (node == lhs) {
                return try analyser.resolveTypeOfNode(options.at(rhs));
            }
            if (node == rhs) {
                return try analyser.resolveTypeOfNode(options.at(lhs));
            }
        },

        .@"return" => {
            const return_expr = tree.nodeData(ancestors[0]).opt_node.unwrap() orelse return null;
            if (node != return_expr) return null;

            var func_buf: [1]Ast.Node.Index = undefined;
            for (1..ancestors.len) |index| {
                const func = tree.fullFnProto(&func_buf, ancestors[index]) orelse continue;
                const return_type = func.ast.return_type.unwrap() orelse continue;
                const return_ty = try analyser.resolveTypeOfNode(options.at(return_type)) orelse return null;
                return try return_ty.instanceTypeVal(analyser);
            }
        },

        .@"continue" => {
            const opt_target, const opt_continue_expr = tree.nodeData(ancestors[0]).opt_token_and_opt_node;
            const target = opt_target.unwrap() orelse return null;
            const continue_expr = opt_continue_expr.unwrap() orelse return null;
            if (node != continue_expr) return null;

            const continue_label = tree.tokenSlice(target);

            const ancestor_switch = for (ancestors[1..]) |ancestor| {
                if (tree.fullSwitch(ancestor)) |switch_node| {
                    const switch_label_token = switch_node.label_token orelse continue;
                    const switch_label = tree.tokenSlice(switch_label_token);
                    if (std.mem.eql(u8, continue_label, switch_label)) {
                        break switch_node;
                    }
                }
            } else {
                return null;
            };

            return try analyser.resolveTypeOfNode(options.at(ancestor_switch.ast.condition));
        },

        .@"break" => {
            const opt_target, const opt_break_expr = tree.nodeData(ancestors[0]).opt_token_and_opt_node;
            const break_expr = opt_break_expr.unwrap() orelse return null;
            if (node != break_expr) return null;

            const break_label_maybe: ?[]const u8 = if (opt_target.unwrap()) |target|
                tree.tokenSlice(target)
            else
                null;

            const index = ast.indexOfBreakTarget(tree, ancestors, break_label_maybe) orelse return null;

            return try analyser.resolveExpressionType(
                options.at(ancestors[index]),
                ancestors[index],
                ancestors[index + 1 ..],
            );
        },

        .grouped_expression,
        .@"try",
        .@"comptime",
        => {
            return try analyser.resolveExpressionType(
                options.at(ancestors[0]),
                ancestors[0],
                ancestors[1..],
            );
        },

        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            var buffer: [2]Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, ancestors[0]).?;
            const call_name = tree.tokenSlice(tree.nodeMainToken(ancestors[0]));

            if (std.mem.eql(u8, call_name, "@as")) {
                if (params.len != 2) return null;
                if (params[1] != node) return null;
                const ty = try analyser.resolveTypeOfNode(options.at(params[0])) orelse return null;
                return try ty.instanceTypeVal(analyser);
            }

            if (version_data.builtins.get(call_name)) |data| {
                const index = std.mem.findScalar(Ast.Node.Index, params, node) orelse return null;
                if (index >= data.parameters.len) return null;
                const parameter = data.parameters[index];
                const colon_index = std.mem.findScalar(u8, parameter.signature, ':') orelse return null;
                const type_str = parameter.signature[colon_index + 2 ..];
                return analyser.resolveLangrefType(type_str);
            }
        },

        .@"orelse" => {
            const lhs, const rhs = tree.nodeData(ancestors[0]).node_and_node;
            if (node == rhs) {
                const lhs_ty = try analyser.resolveTypeOfNode(options.at(lhs)) orelse return null;
                return try analyser.resolveOptionalUnwrap(lhs_ty);
            }
        },

        .@"catch" => {
            const lhs, const rhs = tree.nodeData(ancestors[0]).node_and_node;
            if (node == rhs) {
                const lhs_ty = try analyser.resolveTypeOfNode(options.at(lhs)) orelse return null;
                return try analyser.resolveUnwrapErrorUnionType(lhs_ty, .payload);
            }
        },

        .address_of => {
            std.debug.assert(node == tree.nodeData(ancestors[0]).node);

            const expr_ty = try analyser.resolveExpressionType(
                options.at(ancestors[0]),
                ancestors[0],
                ancestors[1..],
            ) orelse return null;

            if (try analyser.resolveDerefType(expr_ty)) |ty| {
                return ty;
            }

            switch (expr_ty.data) {
                .pointer => |info| switch (info.size) {
                    .slice => {
                        var buffer: [2]Ast.Node.Index = undefined;
                        const array_init = tree.fullArrayInit(&buffer, node) orelse return null;
                        return .{
                            .data = .{
                                .array = .{
                                    .elem_count = array_init.ast.elements.len,
                                    .sentinel = info.sentinel,
                                    .elem_ty = info.elem_ty,
                                },
                            },
                            .is_type_val = false,
                        };
                    },
                    else => {},
                },
                .ip_index => |payload| switch (analyser.ip.indexToKey(payload.type)) {
                    .pointer_type => |pointer_info| switch (pointer_info.flags.size) {
                        .slice => {
                            var buffer: [2]Ast.Node.Index = undefined;
                            const array_init = tree.fullArrayInit(&buffer, node) orelse return null;
                            const ty = try analyser.ip.get(.{
                                .array_type = .{
                                    .len = array_init.ast.elements.len,
                                    .child = pointer_info.elem_type,
                                    .sentinel = pointer_info.sentinel,
                                },
                            });
                            return Type.fromIP(analyser, ty, null);
                        },
                        else => {},
                    },
                    else => {},
                },
                else => {},
            }

            return null;
        },
        .fn_proto_simple,
        .fn_proto_multi,
        .fn_proto_one,
        .fn_proto,
        => {
            var buf: [1]Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buf, ancestors[0]).?;
            if (node.toOptional() == proto.ast.addrspace_expr) {
                return analyser.instanceStdBuiltinType("AddressSpace");
            }
            if (node.toOptional() == proto.ast.callconv_expr) {
                return analyser.instanceStdBuiltinType("CallingConvention");
            }
            if (node.toOptional() == proto.ast.section_expr) {
                const ty = try analyser.ip.get(.{
                    .pointer_type = .{
                        .elem_type = .u8_type,
                        .sentinel = .none,
                        .flags = .{
                            .size = .slice,
                            .is_const = true,
                        },
                    },
                });
                return Type.fromIP(analyser, ty, null);
            }
        },
        .asm_simple,
        .@"asm",
        => {
            const full = tree.fullAsm(ancestors[0]).?;
            if (node.toOptional() == full.ast.clobbers) {
                return analyser.instanceStdBuiltinType("assembly.Clobbers");
            }
        },

        else => {},
    }

    return null;
}

pub fn getSymbolEnumLiteral(
    analyser: *Analyser,
    options: ResolveOptions,
    source_index: usize,
    name: []const u8,
) Error!?struct { DeclWithHandle, ?Type } {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const tree = &options.node_handle.handle.document.tree;
    const nodes = try ast.nodesOverlappingIndex(analyser.arena, tree, source_index);
    if (nodes.len == 0) return null;
    return try analyser.lookupSymbolFieldInit(options, name, nodes[0], nodes[1..]);
}

pub fn resolveStructInitType(
    analyser: *Analyser,
    options: ResolveOptions,
    source_index: usize,
) Error!?Type {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const tree = &options.node_handle.handle.document.tree;
    const nodes = try ast.nodesOverlappingIndex(analyser.arena, tree, source_index);
    if (nodes.len == 0) return null;
    var ty = try analyser.resolveExpressionType(options.at(nodes[0]), nodes[0], nodes[1..]) orelse return null;
    while (true) {
        const unwrapped =
            try analyser.resolveUnwrapErrorUnionType(ty, .payload) orelse
            try analyser.resolveOptionalUnwrap(ty) orelse
            break;
        ty = unwrapped;
    }
    return ty;
}

/// Multiple when using branched types
pub fn getSymbolFieldAccesses(
    analyser: *Analyser,
    arena: std.mem.Allocator,
    handle: DocumentStore.Handle,
    source_index: usize,
    held_loc: offsets.Loc,
    name: []const u8,
) Error!?[]const DeclWithHandle {
    var decls_with_handles: std.ArrayList(DeclWithHandle) = .empty;
    var property_types: std.ArrayList(Type) = .empty;
    try analyser.getSymbolFieldAccessesArrayList(arena, handle, source_index, held_loc, name, &decls_with_handles, &property_types);
    return try decls_with_handles.toOwnedSlice(arena);
}

pub fn getSymbolFieldAccessesArrayList(
    analyser: *Analyser,
    arena: std.mem.Allocator,
    handle: DocumentStore.Handle,
    source_index: usize,
    held_loc: offsets.Loc,
    name: []const u8,
    decls_with_handles: *std.ArrayList(DeclWithHandle),
    property_types: *std.ArrayList(Type),
) Error!void {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (try analyser.getFieldAccessType(handle, source_index, held_loc)) |ty| {
        const container_handle = try analyser.resolveDerefType(ty) orelse ty;

        const container_handle_nodes = try container_handle.getAllTypesWithHandles(analyser);

        for (container_handle_nodes) |t| {
            if (try t.lookupSymbol(analyser, name)) |decl_handle|
                try decls_with_handles.append(arena, decl_handle);
            if (try analyser.resolvePropertyType(ty, name)) |p|
                try property_types.append(arena, p);
        }
    }
}

pub fn getSymbolFieldAccessesHighlight(
    analyser: *Analyser,
    arena: std.mem.Allocator,
    handle: DocumentStore.Handle,
    source_index: usize,
    loc: offsets.Loc,
    decls_with_handles: *std.ArrayList(DeclWithHandle),
    property_types: *std.ArrayList(Type),
) Error!?offsets.Loc {
    const name_loc, const highlight_loc = blk: {
        const name_token, const name_loc = offsets.identifierTokenAndLocFromIndex(&handle.document.tree, source_index) orelse {
            const token = offsets.sourceIndexToTokenIndex(&handle.document.tree, source_index).pickPreferred(&.{ .question_mark, .period_asterisk }, &handle.document.tree) orelse return null;
            switch (handle.document.tree.tokenTag(token)) {
                .question_mark => {
                    const token_loc = offsets.tokenToLoc(&handle.document.tree, token);
                    break :blk .{ token_loc, token_loc };
                },
                .period_asterisk => {
                    var name_loc = offsets.tokenToLoc(&handle.document.tree, token);
                    name_loc.start += 1; // trim the period
                    break :blk .{ name_loc, name_loc };
                },
                else => return null,
            }
        };
        break :blk .{ name_loc, offsets.tokenToLoc(&handle.document.tree, name_token) };
    };
    const name = offsets.locToSlice(handle.document.tree.source, name_loc);
    const held_loc = offsets.locMerge(loc, name_loc);
    try analyser.getSymbolFieldAccessesArrayList(arena, handle, source_index, held_loc, name, decls_with_handles, property_types);
    return highlight_loc;
}

pub const ReferencedType = struct {
    str: []const u8,
    handle: DocumentStore.Handle,
    token: Ast.TokenIndex,

    pub fn of(
        str: []const u8,
        handle: DocumentStore.Handle,
        token: Ast.TokenIndex,
    ) ReferencedType {
        return .{ .str = str, .handle = handle, .token = token };
    }

    pub const Set = std.array_hash_map.Custom(ReferencedType, void, SetContext, true);

    const SetContext = struct {
        pub fn hash(self: SetContext, item: ReferencedType) u32 {
            _ = self;
            var hasher: std.hash.Wyhash = .init(0);
            hasher.update(item.str);
            hasher.update(item.handle.document.uri.raw);
            hasher.update(&std.mem.toBytes(item.token));
            return @truncate(hasher.final());
        }

        pub fn eql(self: SetContext, a: ReferencedType, b: ReferencedType, b_index: usize) bool {
            _ = self;
            _ = b_index;
            return std.mem.eql(u8, a.str, b.str) and
                a.handle.document.uri.eql(b.handle.document.uri) and
                a.token == b.token;
        }
    };
};

// ── Callsite reference finder (inlined from features/references.zig) ──

const CallBuilder = struct {
    callsites: std.ArrayList(NodeWithHandle) = .empty,
    target_decl: DeclWithHandle,
    analyser: *Analyser,

    fn add(self: *CallBuilder, handle: DocumentStore.Handle, call_node: Ast.Node.Index) error{OutOfMemory}!void {
        try self.callsites.append(self.analyser.arena, .{
            .handle = handle,
            .node = call_node,
        });
    }

    fn collectReferences(self: *CallBuilder, handle: DocumentStore.Handle, node: Ast.Node.Index) Error!void {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();
        const arena = self.analyser.arena;
        var walker: ast.Walker = try .init(arena, &handle.document.tree, node);
        defer walker.deinit(arena);
        while (try walker.nextIgnoreClose(arena, &handle.document.tree)) |child| {
            try referenceNode(self, handle, child);
        }
    }

    fn referenceNode(
        builder: *CallBuilder,
        handle: DocumentStore.Handle,
        node: Ast.Node.Index,
    ) Error!void {
        const tree = &handle.document.tree;
        switch (tree.nodeTag(node)) {
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            => {
                var buf: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&buf, node).?;
                const called_node = call.ast.fn_expr;
                switch (tree.nodeTag(called_node)) {
                    .identifier => {
                        const identifier_token = ast.identifierTokenFromIdentifierNode(tree, called_node) orelse return;
                        const child = (try builder.analyser.lookupSymbolGlobal(
                            handle,
                            offsets.identifierTokenToNameSlice(tree, identifier_token),
                            tree.tokenStart(identifier_token),
                        )) orelse return;
                        if (builder.target_decl.eql(child)) {
                            try builder.add(handle, node);
                        }
                    },
                    .field_access => {
                        const lhs_node, const field_name = tree.nodeData(called_node).node_and_token;
                        const lhs = (try builder.analyser.resolveTypeOfNode(.of(lhs_node, handle))) orelse return;
                        const deref_lhs = try builder.analyser.resolveDerefType(lhs) orelse lhs;
                        const symbol = offsets.tokenToSlice(tree, field_name);
                        const child = (try deref_lhs.lookupSymbol(builder.analyser, symbol)) orelse return;
                        if (builder.target_decl.eql(child)) {
                            try builder.add(handle, node);
                        }
                    },
                    else => {},
                }
            },
            else => {},
        }
    }
};

fn callsiteReferences(
    analyser: *Analyser,
    decl_handle: DeclWithHandle,
) Error!std.ArrayList(NodeWithHandle) {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();
    std.debug.assert(decl_handle.decl == .ast_node);
    var builder: CallBuilder = .{
        .analyser = analyser,
        .target_decl = decl_handle,
    };
    try builder.collectReferences(decl_handle.handle, .root);
    return builder.callsites;
}
