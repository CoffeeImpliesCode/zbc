//! Type-expression queries shared by collection and borrow rules.
//!
//! A copied element or aggregate is independent only when its declared
//! type proves that no address travels with it. Unknown types never
//! provide that proof.
//!
//! Everything here is a TOKEN-RANGE question.  A field read can leave
//! the file it was written in, and then the answer is read where the
//! field is declared; a type this walk cannot read is never assumed
//! away, it is charged.  Nothing here allocates: `typePathName` writes
//! into a caller's buffer precisely so a per-call-site question costs
//! no allocation.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");
const file_cache_mod = @import("../cache/file_cache.zig");

/// How far a type expression is followed through nested aggregates
/// before the walk gives up and answers "this file cannot say".
pub const max_element_depth = 4;

/// How many segments of a dotted type path are compared.  A path
/// longer than this is not a name this walk reasons about.
pub const max_path_segments = 8;

/// A type expression in the tree that DECLARED it: a field read can
/// leave this file, and then the answer is read where the field is.
pub const TypeRef = struct {
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    /// Scope that declared this expression, when reached through a field.
    owner: ?file_cache_mod.FileCache.ResolvedType = null,
    /// Borrow checks also inspect inline arrays with nonliteral lengths.
    allow_array_length_expr: bool = false,
};

fn isTypeQualifier(tag: std.zig.Token.Tag) bool {
    return switch (tag) {
        .question_mark, .asterisk, .asterisk_asterisk, .keyword_const, .keyword_volatile, .keyword_allowzero => true,
        else => false,
    };
}

/// The dotted segments of the type path in `ref`, generic argument
/// groups dropped: `std.array_list.Managed(u32)` reads as
/// `["std", "array_list", "Managed"]`.  Returns 0 for anything that is
/// not a plain identifier path — a slice, an array, a call.
pub fn typePathSegments(out: *[max_path_segments][]const u8, ref: TypeRef) usize {
    const tags = ref.tree.tokens.items(.tag);
    var t = ref.first;
    while (t <= ref.last and isTypeQualifier(tags[t])) t += 1;
    if (t > ref.last or tags[t] != .identifier) return 0;
    var count: usize = 0;
    while (true) {
        if (count == max_path_segments) return 0;
        out[count] = ref.tree.tokenSlice(t);
        count += 1;
        t += 1;
        while (t <= ref.last and isTypeQualifier(tags[t])) t += 1;
        // Generic arguments say nothing about WHICH container this is.
        if (t <= ref.last and tags[t] == .l_paren) {
            t = tokens.matchParen(tags, t, ref.last) orelse return 0;
            t += 1;
            while (t <= ref.last and isTypeQualifier(tags[t])) t += 1;
        }
        if (t > ref.last) return count;
        if (tags[t] != .period) return 0;
        t += 1;
        while (t <= ref.last and isTypeQualifier(tags[t])) t += 1;
        if (t > ref.last or tags[t] != .identifier) return 0;
    }
}

/// The dotted name `typePathSegments` read, written into `buf` so no
/// allocation is needed to answer a per-call-site question.
pub fn typePathName(buf: []u8, ref: TypeRef) ?[]const u8 {
    var segments: [max_path_segments][]const u8 = undefined;
    const count = typePathSegments(&segments, ref);
    if (count == 0) return null;
    var len: usize = 0;
    for (segments[0..count], 0..) |segment, i| {
        if (i != 0) {
            if (len + 1 > buf.len) return null;
            buf[len] = '.';
            len += 1;
        }
        if (len + segment.len > buf.len) return null;
        @memcpy(buf[len..][0..segment.len], segment);
        len += segment.len;
    }
    return buf[0..len];
}

pub fn stripPointers(ref: TypeRef) TypeRef {
    const tags = ref.tree.tokens.items(.tag);
    var t = ref.first;
    while (t <= ref.last and (tags[t] == .question_mark or tags[t] == .ampersand or tags[t] == .asterisk)) t += 1;
    var base = ref;
    base.first = t;
    return base;
}

/// Follow a bare container name to the instantiation it aliases:
/// `const List = std.ArrayList(u32)` is the declaration that says what
/// `List` iterates.  A name that resolves to a DECLARED struct is
/// returned unchanged — that is a container, not an alias.
pub fn aliasInitializerRef(cache: *file_cache_mod.FileCache, ref: TypeRef) TypeRef {
    var name_buf: [256]u8 = undefined;
    const name = typePathName(&name_buf, ref) orelse return ref;
    if (std.mem.indexOfScalar(u8, name, '.') != null) return ref;
    if (cache.findTypeAcrossImports(name) != null) return ref;
    for (ref.tree.rootDecls()) |node| {
        const decl = ref.tree.fullVarDecl(node) orelse continue;
        if (!std.mem.eql(u8, ref.tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
        const init = decl.ast.init_node.unwrap() orelse return ref;
        var aliased = ref;
        aliased.first = ref.tree.firstToken(init);
        aliased.last = ref.tree.lastToken(init);
        return aliased;
    }
    return ref;
}

/// The element type a container type expression iterates: the `T` of
/// `[]T`, `[N]T` and `path(T)`, reached through an alias declaration
/// when the container is only named.
pub fn elementTypeRef(cache: *file_cache_mod.FileCache, container: TypeRef, depth: u8) ?TypeRef {
    if (depth > max_element_depth or container.first > container.last) return null;
    const tags = container.tree.tokens.items(.tag);
    if (container.first >= tags.len or container.last >= tags.len) return null;
    var t = container.first;
    while (t <= container.last and (tags[t] == .question_mark or tags[t] == .ampersand)) t += 1;
    if (t > container.last) return null;
    if (tags[t] == .l_bracket) {
        const close = tokens.matchBracket(tags, t, container.last) orelse return null;
        if (close + 1 > container.last) return null;
        var element = container;
        element.first = close + 1;
        return element;
    }
    if (tags[t] != .identifier) return null;
    // The LAST group reaching the end of the expression is the
    // container's own generic argument list; an earlier group is a
    // generic argument of a type this walk steps over.
    var open: ?Ast.TokenIndex = null;
    var k = t;
    while (k <= container.last) : (k += 1) {
        if (tags[k] == .l_paren) open = k;
    }
    if (open) |lp| {
        const rp = tokens.matchParen(tags, lp, container.last) orelse return null;
        if (rp != container.last) return null;
        const arg_first = lp + 1;
        if (arg_first >= rp) return null;
        var nesting: u32 = 0;
        var a = arg_first;
        while (a < rp) : (a += 1) {
            switch (tags[a]) {
                .l_paren, .l_bracket, .l_brace => nesting += 1,
                .r_paren, .r_bracket, .r_brace => nesting -= 1,
                .comma => if (nesting == 0) break,
                else => {},
            }
        }
        // The argument IS the element type expression, not a container
        // to take an element of again.
        var element = container;
        element.first = arg_first;
        element.last = a - 1;
        return element;
    }
    // A bare name only has an element type through the declaration it
    // aliases; a name nothing here declares has none to read.
    const aliased = aliasInitializerRef(cache, container);
    if (aliased.first == container.first and aliased.last == container.last) return null;
    return elementTypeRef(cache, aliased, depth + 1);
}

/// Read the element of an actual two-argument `@Vector` AST call.
/// The declaration's tree supplies both the call and its child; foreign
/// token indices are never handed to the analyzed file's type engine.
fn vectorElementRef(ref: TypeRef, first: Ast.TokenIndex) ?TypeRef {
    if (!std.mem.eql(u8, ref.tree.tokenSlice(first), "@Vector")) return null;
    for (ref.tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        if (ref.tree.nodeMainToken(node) != first or ref.tree.lastToken(node) != ref.last) continue;
        var arguments = @import("type_engine").AstIterator.init(ref.tree, node);
        _ = arguments.next(ref.tree) orelse return null;
        const element_node = arguments.next(ref.tree) orelse return null;
        if (arguments.next(ref.tree) != null) return null;
        var element = ref;
        element.first = ref.tree.firstToken(element_node);
        element.last = ref.tree.lastToken(element_node);
        return element;
    }
    return null;
}

/// Is the type expression PROVEN to carry no address?
///
/// The answer is earned by declarations. A reserved primitive, an enum,
/// a vector of address-free elements, and a struct whose every field is
/// address-free carry no address; a pointer, a slice, a union, and anything
/// this file cannot read are not proved safe.
pub fn typeRangeIsAddressFree(cache: *file_cache_mod.FileCache, ref: TypeRef, depth: u8) bool {
    if (depth > max_element_depth or ref.first > ref.last) return false;
    const tags = ref.tree.tokens.items(.tag);
    if (ref.first >= tags.len or ref.last >= tags.len) return false;
    var t = ref.first;
    while (t <= ref.last and tags[t] == .question_mark) t += 1;
    if (t > ref.last) return false;
    switch (tags[t]) {
        .asterisk, .asterisk_asterisk, .keyword_anyframe => return false,
        // An enum literal is one tag byte.
        .period => return true,
        .keyword_comptime => {
            var payload = ref;
            payload.first = t + 1;
            return typeRangeIsAddressFree(cache, payload, depth);
        },
        .l_bracket => {
            const close = tokens.matchBracket(tags, t, ref.last) orelse return false;
            if (close + 1 > ref.last) return false;
            // A slice or many-pointer is a view; an inline array carries
            // its elements with the value regardless of its length.
            if (close == t + 1 or tags[t + 1] == .colon or tags[t + 1] == .asterisk) return false;
            if (!ref.allow_array_length_expr and !(close == t + 2 and tags[close - 1] == .number_literal)) return false;
            var element = ref;
            element.first = close + 1;
            return typeRangeIsAddressFree(cache, element, depth + 1);
        },
        .builtin => {
            const element = vectorElementRef(ref, t) orelse return false;
            return typeRangeIsAddressFree(cache, element, depth + 1);
        },
        .identifier => {},
        else => return false,
    }
    // Unlike container path queries, this is a type, not a generic
    // instantiation whose arguments may be discarded.
    const name = tokens.typeNameFromTokens(ref.tree, t, ref.last) orelse return false;
    if (isReservedScalarTypeName(name)) return true;
    // `typeNameFromTokens` reads the WHOLE dotted path, so the lookup
    // has to be the one that walks a path: a bare-name lookup is
    // handed `Namespace.Tag` and can never match it, because a
    // declaration is stored under the identifier it was written with.
    const resolved = if (ref.owner) |owner|
        cache.typePathInOwnerScope(owner, name)
    else if (ref.tree == cache.tree)
        cache.resolvedTypePathAcrossImports(name)
    else
        null;
    if (resolved) |owner| {
        switch (owner.info.kind) {
            .enum_ => return true,
            .struct_ => {
                if (owner.info.fields.len == 0) return false;
                for (owner.info.fields) |field| {
                    const field_ref: TypeRef = .{
                        .tree = owner.model.tree,
                        .first = field.type_first,
                        .last = field.type_last,
                        .owner = owner,
                        .allow_array_length_expr = ref.allow_array_length_expr,
                    };
                    if (!typeRangeIsAddressFree(cache, field_ref, depth + 1)) return false;
                }
                return true;
            },
            .union_, .opaque_ => return false,
        }
    }
    // The type engine is anchored to the analyzed tree. Foreign token
    // indices must never be interpreted as positions in that tree.
    if (ref.tree == cache.tree) {
        if (cache.intInfoOfExpr(t, ref.last) != null) return true;
        if (cache.isEnumTypeOfExpr(t, ref.last) == true) return true;
    }
    return false;
}

/// A reserved primitive spelling is the whole proof of an
/// address-free value.  `true` / `false` / `null` / `undefined` spell
/// VALUES, not types, so the reservation settles nothing about a
/// declaration written with one.
pub fn isReservedScalarTypeName(name: []const u8) bool {
    if (!std.zig.primitives.isPrimitive(name)) return false;
    if (std.mem.eql(u8, name, "anyframe")) return false;
    return !std.mem.eql(u8, name, "true") and !std.mem.eql(u8, name, "false") and
        !std.mem.eql(u8, name, "null") and !std.mem.eql(u8, name, "undefined");
}

test "address-free type queries prove vector elements and preserve conservative shapes" {
    const source: [:0]const u8 =
        \\const lanes = @Vector(4, u32);
        \\const boolean_lanes = @Vector(4, bool);
        \\const floating_lanes = @Vector(4, f32);
        \\const optional_lanes = ?@Vector(4, u32);
        \\const pointer_lanes = @Vector(4, *u32);
        \\const optional_pointer_lanes = @Vector(4, ?*u32);
        \\const unknown_lanes = @Vector(4, Missing);
        \\const aggregate_lanes = @Vector(4, AddressBearing);
        \\const unknown_builtin = @TypeOf(missing);
        \\const unknown_this = @This();
        \\const wrong_arity = @Vector(4, u32, u32);
        \\const wrong_builtin = @as(u32, 1);
        \\const scalar = u32;
        \\const optional_scalar = ?u32;
        \\const pointer = *u32;
        \\const optional_pointer = ?*u32;
        \\const array = [4]u32;
        \\const pointer_array = [4]*u32;
        \\const slice = []u32;
        \\const enum_value = Namespace.Tag;
        \\const struct_value = Namespace.Plain;
        \\const borrowed_struct = AddressBearing;
        \\const empty_struct = Empty;
        \\const vector_struct = VectorFields;
        \\const too_deep = [1][1][1][1][1]u32;
        \\const AddressBearing = struct { pointer: *u32 };
        \\const Empty = struct {};
        \\const VectorFields = struct { lanes: @Vector(4, u32) };
        \\const Namespace = struct {
        \\    pub const Tag = enum { a, b };
        \\    pub const Plain = struct { value: u32 };
        \\};
    ;
    var tree = try Ast.parse(std.testing.allocator, source, .zig);
    defer tree.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = file_cache_mod.FileCache.init(std.testing.allocator, &tree);
    defer cache.deinit();
    const cases = [_]struct { name: []const u8, expected: bool }{
        .{ .name = "lanes", .expected = true },
        .{ .name = "boolean_lanes", .expected = true },
        .{ .name = "floating_lanes", .expected = true },
        .{ .name = "optional_lanes", .expected = true },
        .{ .name = "pointer_lanes", .expected = false },
        .{ .name = "optional_pointer_lanes", .expected = false },
        .{ .name = "unknown_lanes", .expected = false },
        .{ .name = "aggregate_lanes", .expected = false },
        .{ .name = "unknown_builtin", .expected = false },
        .{ .name = "unknown_this", .expected = false },
        .{ .name = "wrong_arity", .expected = false },
        .{ .name = "wrong_builtin", .expected = false },
        .{ .name = "scalar", .expected = true },
        .{ .name = "optional_scalar", .expected = true },
        .{ .name = "pointer", .expected = false },
        .{ .name = "optional_pointer", .expected = false },
        .{ .name = "array", .expected = true },
        .{ .name = "pointer_array", .expected = false },
        .{ .name = "slice", .expected = false },
        .{ .name = "enum_value", .expected = true },
        .{ .name = "struct_value", .expected = true },
        .{ .name = "borrowed_struct", .expected = false },
        .{ .name = "empty_struct", .expected = false },
        .{ .name = "vector_struct", .expected = true },
        .{ .name = "too_deep", .expected = false },
    };
    for (cases) |case| {
        var found = false;
        for (tree.rootDecls()) |node| {
            const decl = tree.fullVarDecl(node) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), case.name)) continue;
            const init = decl.ast.init_node.unwrap() orelse return error.MissingInitializer;
            const ref: TypeRef = .{
                .tree = &tree,
                .first = tree.firstToken(init),
                .last = tree.lastToken(init),
            };
            try std.testing.expectEqual(case.expected, typeRangeIsAddressFree(&cache, ref, 0));
            try std.testing.expect(!typeRangeIsAddressFree(&cache, ref, max_element_depth + 1));
            found = true;
            break;
        }
        try std.testing.expect(found);
    }
}

test "vector element queries reuse normalized scalar aliases" {
    const engine = @import("type_engine");
    const source: [:0]const u8 =
        \\const Lane = u32;
        \\const Address = *u32;
        \\const MaybeAddress = ?*u32;
        \\const lanes = @Vector(4, Lane);
        \\const pointer_lanes = @Vector(4, Address);
        \\const optional_pointer_lanes = @Vector(4, MaybeAddress);
        \\const missing_lanes = @Vector(4, Missing);
    ;
    var context: engine.TypeContext = undefined;
    try context.init(std.testing.allocator, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    // A native absolute identity under the working directory. No file is
    // written here; the path only has to be inside the source policy.
    var document_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const directory_len = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &document_path);
    const separator = if (std.mem.endsWith(u8, document_path[0..directory_len], std.fs.path.sep_str)) "" else std.fs.path.sep_str;
    const document_name = try std.fmt.bufPrint(document_path[directory_len..], "{s}zbc-vector-element-aliases.zig", .{separator});
    try resolver.init(&context, std.testing.allocator, document_path[0 .. directory_len + document_name.len], source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = file_cache_mod.FileCache.init(std.testing.allocator, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const cases = [_]struct { name: []const u8, expected: bool }{
        .{ .name = "lanes", .expected = true },
        .{ .name = "pointer_lanes", .expected = false },
        .{ .name = "optional_pointer_lanes", .expected = false },
        .{ .name = "missing_lanes", .expected = false },
    };
    for (cases) |case| {
        var found = false;
        for (tree.rootDecls()) |node| {
            const decl = tree.fullVarDecl(node) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), case.name)) continue;
            const init = decl.ast.init_node.unwrap() orelse return error.MissingInitializer;
            try std.testing.expectEqual(case.expected, typeRangeIsAddressFree(&cache, .{
                .tree = tree,
                .first = tree.firstToken(init),
                .last = tree.lastToken(init),
            }, 0));
            found = true;
            break;
        }
        try std.testing.expect(found);
    }
}

test "vector fields are queried in their declaring tree and owner" {
    const declaring_source: [:0]const u8 =
        \\const Scalar = *u32;
        \\const Owner = struct {
        \\    const Payload = struct { address: *u32 };
        \\    lanes: @Vector(4, u32),
        \\    pointer_lanes: @Vector(4, *u32),
        \\    optional_pointer_lanes: @Vector(4, ?*u32),
        \\    unknown_lanes: @Vector(4, Missing),
        \\    borrowed_lanes: @Vector(4, Payload),
        \\    shadowed_lanes: @Vector(4, Scalar),
        \\};
    ;
    const analyzed_source: [:0]const u8 =
        \\const Scalar = u32;
        \\const Missing = u32;
        \\const Payload = struct { value: u32 };
        \\const Owner = struct { lanes: u32 };
    ;
    var declaring_tree = try Ast.parse(std.testing.allocator, declaring_source, .zig);
    defer declaring_tree.deinit(std.testing.allocator);
    var declaring_cache = file_cache_mod.FileCache.init(std.testing.allocator, &declaring_tree);
    defer declaring_cache.deinit();
    var analyzed_tree = try Ast.parse(std.testing.allocator, analyzed_source, .zig);
    defer analyzed_tree.deinit(std.testing.allocator);
    var analyzed_cache = file_cache_mod.FileCache.init(std.testing.allocator, &analyzed_tree);
    defer analyzed_cache.deinit();
    const owner = declaring_cache.resolvedTypeAcrossImports("Owner") orelse return error.OwnerNotFound;
    try std.testing.expect(owner.model.tree == &declaring_tree);
    for (owner.info.fields) |field| {
        const ref: TypeRef = .{
            .tree = owner.model.tree,
            .first = field.type_first,
            .last = field.type_last,
            .owner = owner,
        };
        const expected = std.mem.eql(u8, field.name, "lanes");
        try std.testing.expectEqual(expected, typeRangeIsAddressFree(&analyzed_cache, ref, 0));
    }
    try std.testing.expectEqual(@as(usize, 6), owner.info.fields.len);
}
