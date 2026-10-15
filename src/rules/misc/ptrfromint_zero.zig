//! Detects `@ptrFromInt(0)` — creating a non-nullable pointer from the
//! null address.
//!
//! In Zig, non-nullable pointer types (`*T`, `[*]T`, `*const T`, etc.)
//! must never hold the value 0.  `@ptrFromInt(0)` manufactures a pointer
//! to address 0, which is undefined behaviour on every major platform —
//! dereferencing it traps in Debug/ReleaseSafe and produces silent memory
//! corruption in ReleaseFast.
//!
//! If you need a sentinel "no pointer" value, use an optional: `?*T` with
//! `null`.  If you need an untyped zero-address for pointer arithmetic
//! (e.g., to compute an offset), use `@as(usize, 0)` and stay in integer
//! space until you have a valid base address.
//!
//! Real-world shape: common when porting C code that passes NULL as a
//! sentinel or placeholder; also seen in unsafe FFI bridges that try to
//! represent an "empty" struct pointer.
//!
//! Detection (Tier 1, token walk):
//!   4-token pattern: `builtin("@ptrFromInt") l_paren number_literal("0") r_paren`
//!   Fire at the `@ptrFromInt` builtin token.
//!   Exempt only an exact destination pointer that permits address zero.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ptrfromint-zero";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ptrfromint_zero)) return;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 3 <= last_tok) : (t += 1) {
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@ptrFromInt")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .number_literal) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "0")) continue;
        if (tags[t + 3] != .r_paren) continue;

        if (try targetAllowsZero(tree, cache, t)) continue;

        try report(gpa, problems, tree, t);
    }
}

/// The contextual type engine owns aliases and aggregate field destinations.
/// Without it, only a direct literal type annotation can prove `allowzero`.
fn targetAllowsZero(tree: *const Ast, cache: *file_cache_mod.FileCache, token: Ast.TokenIndex) !bool {
    const node = cache.nodeForExactSpan(token, token + 3) orelse return false;
    if (cache.zls) |resolver| {
        const destination = (try resolver.resolutionFrame().expectedTypeOfNode(node)) orelse return false;
        return resolver.pointerAllowsZero(destination) orelse false;
    }

    var buffer: [2]Ast.Node.Index = undefined;
    for (tree.nodes.items(.tag), 0..) |tag, raw_parent| {
        const parent: Ast.Node.Index = @enumFromInt(raw_parent);
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(parent)), "@as")) continue;
                const args = tree.builtinCallParams(&buffer, parent) orelse continue;
                if (args.len != 2 or args[1] != node) continue;
                return literalAllowsZero(tree, args[0]);
            },
            .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {
                const declaration = tree.fullVarDecl(parent).?;
                if (declaration.ast.init_node != node.toOptional()) continue;
                return literalAllowsZero(tree, declaration.ast.type_node.unwrap() orelse return false);
            },
            else => {},
        }
    }
    return false;
}

fn literalAllowsZero(tree: *const Ast, node: Ast.Node.Index) bool {
    const pointer = tree.fullPtrType(node) orelse return false;
    return pointer.allowzero_token != null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    builtin_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@ptrFromInt(0)` creates a null pointer to a non-nullable type — dereferencing it is undefined behaviour on every platform (trap in Debug/Safe, silent corruption in ReleaseFast); use `?*T` with `null` for a sentinel, or stay in `usize` for offset arithmetic",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, builtin_tok),
        .end = try Pos.fromTokenEnd(tree, builtin_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "ptrfromint-zero: bare zero fires" {
    try testing.expectFires(check, R,
        \\fn nullPtr() *u8 {
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
}

test "ptrfromint-zero: non-zero does not fire" {
    try testing.expectNoFire(check,
        \\fn mmioPtr(addr: usize) *volatile u32 {
        \\    return @ptrFromInt(addr);
        \\}
        \\
    );
}

test "ptrfromint-zero: non-zero literal does not fire" {
    try testing.expectNoFire(check,
        \\fn fixedAddr() *u32 {
        \\    return @ptrFromInt(0x1000_0000);
        \\}
        \\
    );
}

test "ptrfromint-zero: allowzero cast target does not fire" {
    try testing.expectNoFire(check,
        \\fn nullSentinel() *allowzero u0 {
        \\    return @as(*allowzero u0, @ptrFromInt(0));
        \\}
        \\
    );
}

test "ptrfromint-zero: allowzero var-decl target does not fire" {
    try testing.expectNoFire(check,
        \\fn nullSentinel() void {
        \\    const p: *allowzero u8 = @ptrFromInt(0);
        \\    _ = p;
        \\}
        \\
    );
}

test "ptrfromint-zero: non-allowzero @as still fires" {
    try testing.expectFires(check, R,
        \\fn bad() *u8 {
        \\    return @as(*u8, @ptrFromInt(0));
        \\}
        \\
    );
}

test "ptrfromint-zero: contextual C pointer cast permits zero" {
    try testing.expectNoFireTyped(check,
        \\fn sentinel() [*c]const u8 {
        \\    return @as([*c]const u8, @ptrFromInt(0));
        \\}
    );
}

test "ptrfromint-zero: contextual C pointer local permits zero" {
    try testing.expectNoFireTyped(check,
        \\fn sentinel() void {
        \\    const p: [*c]const u8 = @ptrFromInt(0);
        \\    _ = p;
        \\}
    );
}

test "ptrfromint-zero: contextual C pointer return permits zero" {
    try testing.expectNoFireTyped(check,
        \\fn sentinel() [*c]const u8 {
        \\    return @ptrFromInt(0);
        \\}
    );
}

test "ptrfromint-zero: contextual returned aggregate field permits zero" {
    try testing.expectNoFireTyped(check,
        \\const Value = union(enum) { text: []const u8, none, number: f64 };
        \\const present_empty_value: [1]u8 = .{0};
        \\fn valueSliceOf(value: Value) struct { ptr: [*c]const u8, len: usize } {
        \\    return switch (value) {
        \\        .text => |text| if (text.len == 0)
        \\            .{ .ptr = &present_empty_value, .len = 0 }
        \\        else
        \\            .{ .ptr = text.ptr, .len = text.len },
        \\        .none, .number => .{ .ptr = @ptrFromInt(0), .len = 0 },
        \\    };
        \\}
    );
}

test "ptrfromint-zero: contextual actual bridge cast shape permits zero" {
    try testing.expectNoFireTyped(check,
        \\const Value = union(enum) { text: []const u8, none, number: f64 };
        \\fn valueSliceOf(value: Value) struct { ptr: [*c]const u8, len: usize } {
        \\    return switch (value) {
        \\        .text => |text| .{ .ptr = text.ptr, .len = text.len },
        \\        .none, .number => .{ .ptr = @as([*c]const u8, @ptrFromInt(0)), .len = 0 },
        \\    };
        \\}
    );
}

test "ptrfromint-zero: contextual current file aliases preserve C pointer" {
    try testing.expectNoFireTyped(check,
        \\const P = [*c]const u8;
        \\const Alias = P;
        \\const Slice = struct { ptr: Alias, len: usize };
        \\fn sentinel() Slice { return .{ .ptr = @ptrFromInt(0), .len = 0 }; }
    );
}

test "ptrfromint-zero: contextual allowzero return permits zero" {
    try testing.expectNoFireTyped(check,
        \\fn sentinel() *allowzero u8 { return @ptrFromInt(0); }
    );
}

test "ptrfromint-zero: contextual allowzero aliases permit zero" {
    try testing.expectNoFireTyped(check,
        \\const P = *allowzero u8;
        \\const Alias = P;
        \\fn sentinel() Alias { return @ptrFromInt(0); }
    );
}

test "ptrfromint-zero: contextual ordinary pointer return still fires" {
    try testing.expectFiresTyped(check, R,
        \\fn invalid() *u8 { return @ptrFromInt(0); }
    );
}

test "ptrfromint-zero: contextual ordinary as target still fires" {
    try testing.expectFiresTyped(check, R,
        \\fn invalid() *u8 { return @as(*u8, @ptrFromInt(0)); }
    );
}

test "ptrfromint-zero: contextual C pointer sibling cannot hide ordinary field" {
    try testing.expectFiresTyped(check, R,
        \\fn invalid(p: [*c]u8) struct { nullable: [*c]u8, required: *u8 } {
        \\    return .{ .nullable = p, .required = @ptrFromInt(0) };
        \\}
    );
}

test "ptrfromint-zero: contextual previous allowzero operand cannot hide ordinary argument" {
    try testing.expectFiresTyped(check, R,
        \\fn consume(nullable: *allowzero u8, required: *u8) void { _ = nullable; _ = required; }
        \\fn invalid() void {
        \\    consume(@as(*allowzero u8, undefined), @ptrFromInt(0));
        \\}
    );
}

test "ptrfromint-zero: contextual nested allowzero pointee cannot hide ordinary pointer" {
    try testing.expectFiresTyped(check, R,
        \\fn invalid() **allowzero u8 { return @as(**allowzero u8, @ptrFromInt(0)); }
    );
}

test "ptrfromint-zero: contextual unresolved target stays conservative" {
    try testing.expectFiresTyped(check, R,
        \\fn invalid() Missing { return @ptrFromInt(0); }
    );
}

fn expectImportedPointer(source: [:0]const u8, expected: usize) !void {
    const engine = @import("type_engine");
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "api.zig",
        .data =
        \\pub const CPointer = [*c]const u8;
        \\pub const Alias = CPointer;
        \\pub const Slice = struct { ptr: Alias, len: usize };
        \\pub const Required = *u8;
        ,
    });
    const directory = try tmp.dir.realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    cache.setZls(&resolver);
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(expected, problems.items.len);
    for (problems.items) |finding| try std.testing.expectEqualStrings(R, finding.rule_id);
}

test "ptrfromint-zero: contextual imported alias field permits zero" {
    try expectImportedPointer(
        \\const api = @import("api.zig");
        \\fn sentinel() api.Slice { return .{ .ptr = @ptrFromInt(0), .len = 0 }; }
    , 0);
}

test "ptrfromint-zero: contextual imported ordinary alias still fires" {
    try expectImportedPointer(
        \\const api = @import("api.zig");
        \\fn invalid() api.Required { return @ptrFromInt(0); }
    , 1);
}
