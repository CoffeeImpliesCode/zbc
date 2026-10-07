//! Diagnose returned views and propagated values that borrow runtime frame storage.
//! Bare scalar addresses belong to stack-escape; address-free copies and
//! container-level variables carry no frame loan.

const std = @import("std");
const Ast = std.zig.Ast;
const tokens = @import("../../ast/tokens.zig");
const returned_storage = @import("../../cache/return_storage.zig");
const Iterator = @import("type_engine").AstIterator;
const TypeResolver = @import("type_engine").TypeResolver;
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "borrowed-slice-into-stack-buffer-returned";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .borrowed_slice_into_stack_buffer_returned)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    // A copied scalar or address-free aggregate cannot return a storage loan.
    if (cache.zls) |resolver| {
        if (proto.ast.return_type.unwrap()) |node| {
            const frame = resolver.resolutionFrame();
            if (try frame.typeOfNode(node)) |actual| {
                if (try typeIsAddressFree(frame, actual, 0)) return;
            }
        }
    }
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    if (!tokens.hasTokenInRange(tags, first, last, .keyword_return)) return;

    // Query frames and immutable loan arrays borrow this function arena.
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var query = returned_storage.ExpressionLoanQuery.init(.{
        .cache = cache,
        .body = body,
        .scratch = &arena,
    });
    var pending: std.ArrayList(Ast.Node.Index) = .empty;
    defer pending.deinit(gpa);
    try pending.append(gpa, body);
    while (pending.pop()) |node| {
        if (tree.nodeTag(node) == .fn_decl) continue;
        var container_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&container_buffer, node) != null) continue;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
            const loans = try query.expressionLoansAt(.{
                .selection = .{ .node = value },
                .horizon = tree.firstToken(value),
            });
            for (loans.loans) |loan| {
                if (loan.origin != .frame_cell) continue;
                if (!try bindingIsRuntimeLocal(cache, body, loan.binding_token)) continue;
                if (loan.derivation == .direct_address and loan.scalar_cell) continue;
                try report(gpa, problems, tree, tree.nodeMainToken(node), tree.tokenSlice(loan.binding_token));
                break;
            }
            continue;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| try pending.append(gpa, child);
    }
}

/// Resolve every payload through its owner frame; unknown fields refuse the
/// proof. This also handles unions and wrappers around address-free values.
fn typeIsAddressFree(
    frame: TypeResolver.ResolutionFrame,
    value: TypeResolver.ActualType,
    depth: u8,
) file_cache_mod.SummaryError!bool {
    if (depth >= 32) return false;
    const resolver = frame.resolver;
    const actual = (try resolver.normalizedType(value)) orelse return false;
    switch (resolver.typeTag(actual) orelse return false) {
        .int, .float, .comptime_int, .comptime_float, .bool, .@"enum", .void, .noreturn, .null, .error_set => return true,
        .optional, .error_union, .array, .vector => {
            const child = resolver.childType(actual) orelse return false;
            return typeIsAddressFree(frame, child, depth + 1);
        },
        .@"struct", .@"union" => {
            if (actual.data != .container) return false;
            const container = actual.data.container;
            const owner = resolver.frameForContainer(container);
            const tree = &owner.handle.document.tree;
            var buffer: [2]Ast.Node.Index = undefined;
            const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
            for (declaration.ast.members) |member| {
                const field = tree.fullContainerField(member) orelse continue;
                const type_node = field.ast.type_expr.unwrap() orelse return false;
                const field_type = (try owner.typeOfNode(type_node)) orelse return false;
                if (!try typeIsAddressFree(owner, field_type, depth + 1)) return false;
            }
            return true;
        },
        else => return false,
    }
}

/// A declaration in a local type still has static storage. Follow the AST
/// ancestry, not the lexical function token range used by binding collection.
fn bindingIsRuntimeLocal(cache: *file_cache_mod.FileCache, body: Ast.Node.Index, token: Ast.TokenIndex) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    if (token < tree.firstToken(body) or token > tree.lastToken(body)) return false;
    var node = body;
    while (true) {
        if (tree.nodeTag(node) == .fn_decl) return false;
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&buffer, node) != null) return false;
        if (tree.fullVarDecl(node)) |variable| {
            if (token == variable.ast.mut_token + 1) {
                if (variable.ast.init_node.unwrap()) |initializer| {
                    // Type expressions have no runtime cell. Use the actual
                    // initializer, since a declaration name is not an AST node.
                    var container_buffer: [2]Ast.Node.Index = undefined;
                    if (tree.fullContainerDecl(&container_buffer, initializer) != null) return false;
                    if (cache.zls) |resolver| {
                        // typeOfNode normalizes runtime values into type values.
                        // Only the initializer's raw value can prove a type alias.
                        if (try resolver.resolutionFrame().resolveValueOfNode(initializer)) |actual| {
                            if (actual.is_type_val) return false;
                        }
                    }
                }
            }
        }
        var children = Iterator.init(tree, node);
        node = while (children.next(tree)) |child| {
            if (token >= tree.firstToken(child) and token <= tree.lastToken(child)) break child;
        } else return true;
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    return_tok: Ast.TokenIndex,
    tainted_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "the returned value carries storage borrowed from stack-local buffer `{s}`; the buffer dies at function return, leaving dangling pointers or slices. Clone the borrowed data (or remove the borrowing fields) before returning",
        .{tainted_name},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, return_tok),
        .end = try Pos.fromTokenEnd(tree, return_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "bare scalar address belongs to direct stack escape rather than borrowed storage" {
    try testing.expectNoFireTyped(check,
        \\pub fn pointer() *u32 {
        \\    var value: u32 = 7;
        \\    return &value;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn pointer() *u32 {
        \\    var value: u32 = 7;
        \\    return (&value);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\var value: u32 = 7;
        \\pub fn pointer() *u32 { return &value; }
    );
    try testing.expectNoFireTyped(check,
        \\pub fn pointer(external: *u32) *u32 { return external; }
    );
}

test "scalar pointer propagation establishes a derived storage origin" {
    try testing.expectFiresTyped(check, R,
        \\pub fn pointer() *u32 {
        \\    var value: u32 = 7;
        \\    const loan = &value;
        \\    return loan;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn pointer(external: *u32) *u32 {
        \\    const loan = external;
        \\    return loan;
        \\}
    );
}

test "wrapped scalar pointer is borrowed storage despite its scalar pointee" {
    try testing.expectFiresTyped(check, R,
        \\const Wrapped = struct { pointer: *u32 };
        \\fn wrap(pointer: *u32) Wrapped { return .{ .pointer = pointer }; }
        \\pub fn pointer() Wrapped {
        \\    var value: u32 = 7;
        \\    return wrap(&value);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Wrapped = struct { pointer: *u32 };
        \\fn wrap(pointer: *u32) Wrapped { return .{ .pointer = pointer }; }
        \\pub fn pointer(external: *u32) Wrapped { return wrap(external); }
    );
}

test "selected scalar pointer payload preserves its derived storage origin" {
    try testing.expectFiresTyped(check, R,
        \\pub fn pointer() *u32 {
        \\    var value: u32 = 7;
        \\    const payload: [1]*u32 = .{&value};
        \\    return payload[0];
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn pointer(external: *u32) *u32 {
        \\    const payload: [1]*u32 = .{external};
        \\    return payload[0];
        \\}
    );
}

test "SemanticVersion.parse pattern fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const SemanticVersion = struct {
        \\    pre: ?[]const u8 = null,
        \\    build: ?[]const u8 = null,
        \\    pub fn parse(text: []const u8) SemanticVersion { return .{ .pre = text }; }
        \\};
        \\pub fn detect() SemanticVersion {
        \\    var buf: [64]u8 = undefined;
        \\    const ver = SemanticVersion.parse(&buf);
        \\    return ver;
        \\}
    );
}

test "parse on a non-stack-buf doesn't fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const SemanticVersion = struct {
        \\    pub fn parse(_: []const u8) SemanticVersion { return .{}; }
        \\};
        \\pub fn detect(text: []const u8) SemanticVersion {
        \\    const ver = SemanticVersion.parse(text);
        \\    return ver;
        \\}
    );
}

test "parse result not returned doesn't fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const SemanticVersion = struct {
        \\    pub fn parse(_: []const u8) SemanticVersion { return .{}; }
        \\};
        \\pub fn detect() void {
        \\    var buf: [64]u8 = undefined;
        \\    const ver = SemanticVersion.parse(&buf);
        \\    _ = ver;
        \\}
    );
}

// Canonical returned-storage consumer boundaries.

test "summary: free fn returning arg[a..] of a stack buf, returned, fires" {
    try testing.expectFiresTyped(check, R,
        \\fn subslice(buf: []u8) []u8 { return buf[1..]; }
        \\pub fn detect() []u8 {
        \\    var b: [16]u8 = undefined;
        \\    const s = subslice(&b);
        \\    return s;
        \\}
    );
}

test "summary: static method returning arg[a..] of a stack buf, returned, fires" {
    try testing.expectFiresTyped(check, R,
        \\const Slicer = struct {
        \\    fn subslice(buf: []u8) []u8 { return buf[1..]; }
        \\};
        \\pub fn detect() []u8 {
        \\    var b: [16]u8 = undefined;
        \\    const s = Slicer.subslice(&b);
        \\    return s;
        \\}
    );
}

test "summary: allocating callee (returns owned/heap) does not fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn dupe(gpa: std.mem.Allocator, buf: []u8) []u8 {
        \\    const r = gpa.alloc(u8, buf.len) catch unreachable;
        \\    @memcpy(r, buf);
        \\    return r;
        \\}
        \\pub fn detect(gpa: std.mem.Allocator) []u8 {
        \\    var b: [16]u8 = undefined;
        \\    const s = dupe(gpa, &b);
        \\    return s;
        \\}
    );
}

test "summary: borrowed value COPIED through an allocating call before return does not fire" {
    // The resourcesdir.zig shape: `v` borrows the stack buffer, but is passed
    // through `join(alloc, ...)` which copies it into a fresh allocation, so the
    // returned value does not alias the dead buffer.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn subslice(buf: []u8) []u8 { return buf[1..]; }
        \\fn join(a: std.mem.Allocator, parts: []const []const u8) []u8 {
        \\    var len: usize = 0;
        \\    for (parts) |part| len += part.len;
        \\    const result = a.alloc(u8, len) catch unreachable;
        \\    var offset: usize = 0;
        \\    for (parts) |part| {
        \\        @memcpy(result[offset..][0..part.len], part);
        \\        offset += part.len;
        \\    }
        \\    return result;
        \\}
        \\pub fn detect(alloc: std.mem.Allocator) []u8 {
        \\    var b: [16]u8 = undefined;
        \\    const v = subslice(&b);
        \\    return join(alloc, &.{ v, "x" });
        \\}
    );
}

test "unresolved copying call retains a possible stack borrow" {
    try testing.expectFiresTyped(check, R,
        \\fn detect(copy: *const fn ([]u8) []u8) []u8 {
        \\    var buf: [2]u8 = undefined;
        \\    return copy(&buf);
        \\}
    );
}

test "allocation-like name does not prove independent storage" {
    try testing.expectFiresTyped(check, R,
        \\const Borrower = struct {
        \\    fn alloc(_: Borrower, value: []u8) []u8 { return value; }
        \\};
        \\fn detect() []u8 {
        \\    var buf: [2]u8 = undefined;
        \\    const borrower: Borrower = .{};
        \\    return borrower.alloc(&buf);
        \\}
    );
}

test "summary: borrowed_from a NON-buffer arg does not fire" {
    try testing.expectNoFireTyped(check,
        \\fn subslice(buf: []u8) []u8 { return buf[1..]; }
        \\pub fn detect(input: []u8) []u8 {
        \\    var b: [16]u8 = undefined;
        \\    _ = &b;
        \\    const s = subslice(input);
        \\    return s;
        \\}
    );
}

test "by-value array copy and scalar projection do not escape storage" {
    try testing.expectNoFireTyped(check,
        \\fn copy(value: [2]u8) [2]u8 { return value; }
        \\fn detect() u8 {
        \\    var partial: [2]u8 = undefined;
        \\    partial[0] = 7;
        \\    const picked = copy(partial);
        \\    return picked[1];
        \\}
    );
}

test "borrowed slice scalar projection does not escape storage" {
    try testing.expectNoFireTyped(check,
        \\fn borrow(value: []u8) []u8 { return value; }
        \\fn detect() u8 {
        \\    var buf: [2]u8 = undefined;
        \\    const picked = borrow(&buf);
        \\    return picked[1];
        \\}
    );
}

test "nested borrowed field escapes storage" {
    try testing.expectFiresTyped(check, R,
        \\const Result = struct { nested: struct { bytes: []u8 }, count: usize };
        \\fn borrow(value: []u8) Result {
        \\    return .{ .nested = .{ .bytes = value }, .count = value.len };
        \\}
        \\fn detect() []u8 {
        \\    var buf: [2]u8 = undefined;
        \\    const picked = borrow(&buf);
        \\    return picked.nested.bytes;
        \\}
    );
}

test "nonborrowed result field does not escape nested storage" {
    try testing.expectNoFireTyped(check,
        \\const Result = struct { nested: struct { bytes: []u8 }, count: usize };
        \\fn borrow(value: []u8) Result {
        \\    return .{ .nested = .{ .bytes = value }, .count = value.len };
        \\}
        \\fn detect() usize {
        \\    var buf: [2]u8 = undefined;
        \\    const picked = borrow(&buf);
        \\    return picked.count;
        \\}
    );
}

test "returned slice forwarded through a call still escapes" {
    try testing.expectFiresTyped(check, R,
        \\fn borrow(value: []u8) []u8 { return value; }
        \\fn detect() []u8 {
        \\    var buf: [2]u8 = undefined;
        \\    const picked = borrow(&buf);
        \\    return borrow(picked);
        \\}
    );
}

test "by-value pointer-free array return does not escape storage" {
    try testing.expectNoFireTyped(check,
        \\fn copy(value: [2]u8) [2]u8 { return value; }
        \\fn detect() [2]u8 {
        \\    var buf: [2]u8 = undefined;
        \\    return copy(buf);
        \\}
    );
}

test "value receiver formal maps to its actual borrowed field" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct {
        \\    bytes: []u8,
        \\    fn get(self: View) []u8 { return self.bytes; }
        \\};
        \\fn detect() []u8 {
        \\    var buf: [2]u8 = undefined;
        \\    const view: View = .{ .bytes = &buf };
        \\    return view.get();
        \\}
    );
}

test "returned pointer still escapes stack storage" {
    try testing.expectFiresTyped(check, R,
        \\fn borrow(value: *[2]u8) *[2]u8 { return value; }
        \\fn detect() *[2]u8 {
        \\    var buf: [2]u8 = undefined;
        \\    return borrow(&buf);
        \\}
    );
}

test "borrowed pointer array cell does not lend its external pointer payload" {
    try testing.expectNoFireTyped(check,
        \\fn borrow(value: []*u8) []*u8 { return value; }
        \\fn detect(external: *u8) *u8 {
        \\    var buf: [2]*u8 = undefined;
        \\    buf = .{ external, external };
        \\    const picked = borrow(&buf);
        \\    return picked[1];
        \\}
    );
}

test "borrowed pointer array payload follows a later local pointer assignment" {
    try testing.expectFiresTyped(check, R,
        \\fn borrow(value: []*u8) []*u8 { return value; }
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    pointers = .{&local};
        \\    return borrow(&pointers)[0];
        \\}
    );
}

test "unknown pointer array result can reinterpret its outer array address" {
    try testing.expectFiresTyped(check, R,
        \\fn detect(external: *u8, read: *const fn ([]*u8) []*u8) *u8 {
        \\    var pointers: [1]*u8 = .{external};
        \\    return read(&pointers)[0];
        \\}
    );
}

test "returned pointer array cell address remains stack storage" {
    try testing.expectFiresTyped(check, R,
        \\fn identity(values: *[1]*u8) *[1]*u8 { return values; }
        \\fn detect(external: *u8) *[1]*u8 {
        \\    var pointers: [1]*u8 = .{external};
        \\    return identity(&pointers);
        \\}
    );
}

test "known pointer array reinterpretation retains its outer cell" {
    try testing.expectFiresTyped(check, R,
        \\fn reinterpret(values: []*u8) *u8 { return @ptrCast(values.ptr); }
        \\fn detect(external: *u8) *u8 {
        \\    var pointers: [1]*u8 = .{external};
        \\    return reinterpret(&pointers);
        \\}
    );
}

test "known pointer array element reader copies external payload" {
    try testing.expectNoFireTyped(check,
        \\fn read(values: []*u8) *u8 { return values[0]; }
        \\fn detect(external: *u8) *u8 {
        \\    var pointers: [1]*u8 = .{external};
        \\    return read(&pointers);
        \\}
    );
}

test "known pointer array element reader retains local payload" {
    try testing.expectFiresTyped(check, R,
        \\fn read(values: []*u8) *u8 { return values[0]; }
        \\fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{&local};
        \\    return read(&pointers);
        \\}
    );
}

test "known pointer cell dereference copies external payload" {
    try testing.expectNoFireTyped(check,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\fn detect(external: *u8) *u8 {
        \\    var pointer = external;
        \\    return read(&pointer);
        \\}
    );
}

test "known pointer cell dereference retains local payload" {
    try testing.expectFiresTyped(check, R,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = &local;
        \\    return read(&pointer);
        \\}
    );
}

test "borrowed pointer array payload follows an element store" {
    try testing.expectFiresTyped(check, R,
        \\fn borrow(value: []*u8) []*u8 { return value; }
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    pointers[0] = &local;
        \\    return borrow(&pointers)[0];
        \\}
    );
}

test "pointer array element with a real stack borrow escapes" {
    try testing.expectFiresTyped(check, R,
        \\fn detect() *[2]u8 {
        \\    var buf: [2]u8 = undefined;
        \\    const pointers = .{ &buf, &buf };
        \\    return pointers[1];
        \\}
    );
}

test "initialized array address remains stack storage" {
    try testing.expectFiresTyped(check, R,
        \\fn detect() []const u8 {
        \\    const buf = [_]u8{0} ** 2;
        \\    return &buf;
        \\}
    );
}

test "initialized array slice remains stack storage" {
    try testing.expectFiresTyped(check, R,
        \\fn detect() []const u8 {
        \\    var buf = [_]u8{0} ** 2;
        \\    return buf[0..];
        \\}
    );
}

test "initialized array by-value return remains independent" {
    try testing.expectNoFireTyped(check,
        \\fn detect() [2]u8 {
        \\    const buf = [_]u8{0} ** 2;
        \\    return buf;
        \\}
    );
}

test "clearing all copied borrowing fields removes storage" {
    try testing.expectNoFireTyped(check,
        \\const View = struct { pre: ?[]const u8, build: ?[]const u8 };
        \\fn parse(input: []const u8) View { return .{ .pre = input, .build = input }; }
        \\fn detect() View {
        \\    const buf = [_]u8{0} ** 2;
        \\    const original = parse(&buf);
        \\    var copy = original;
        \\    copy.pre = null;
        \\    copy.build = null;
        \\    return copy;
        \\}
    );
}

test "partial borrowing field clear retains the other field" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8, build: ?[]const u8 };
        \\fn parse(input: []const u8) View { return .{ .pre = input, .build = input }; }
        \\fn detect() View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var view = parse(&buf);
        \\    view.pre = null;
        \\    return view;
        \\}
    );
}

test "conditional borrowing field clear retains storage" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8 };
        \\fn detect(clear: bool) View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var view: View = .{ .pre = &buf };
        \\    if (clear) view.pre = null;
        \\    return view;
        \\}
    );
}

test "unknown mutation after borrowing field clear retains storage" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8 };
        \\fn detect(mutate: *const fn (*View) void) View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var view: View = .{ .pre = &buf };
        \\    view.pre = null;
        \\    mutate(&view);
        \\    return view;
        \\}
    );
}

test "conditional rebind after borrowing field clear retains storage" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8 };
        \\fn detect(rebind: bool) View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var view: View = .{ .pre = &buf };
        \\    view.pre = null;
        \\    if (rebind) view = .{ .pre = &buf };
        \\    return view;
        \\}
    );
}

test "field assignment introduces a borrow into an initially empty carrier" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8 = null };
        \\fn detect() View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var view: View = .{};
        \\    view.pre = &buf;
        \\    return view;
        \\}
    );
}

test "cleared slice fields do not remove a residual borrowed pointer" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8, build: ?[]const u8, pointer: *const [2]u8 };
        \\fn detect() View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var view: View = .{ .pre = &buf, .build = &buf, .pointer = &buf };
        \\    view.pre = null;
        \\    view.build = null;
        \\    return view;
        \\}
    );
}

test "material copy keeps the source borrow before later source clearing" {
    try testing.expectFiresTyped(check, R,
        \\const View = struct { pre: ?[]const u8 };
        \\fn detect() View {
        \\    const buf = [_]u8{0} ** 2;
        \\    var original: View = .{ .pre = &buf };
        \\    const copy = original;
        \\    original.pre = null;
        \\    return copy;
        \\}
    );
}

test "initialized array scalar copy does not escape storage" {
    try testing.expectNoFireTyped(check,
        \\fn detect() u8 {
        \\    const buf = [_]u8{7} ** 2;
        \\    const copy = buf;
        \\    return copy[1];
        \\}
    );
}

test "unknown pointer array copier retains actual element storage" {
    try testing.expectFiresTyped(check, R,
        \\fn detect(copy: *const fn ([1]*u8) [1]*u8) *u8 {
        \\    var local: u8 = 1;
        \\    return copy(.{&local})[0];
        \\}
    );
}

test "formal field pointer array forwarding retains element storage" {
    try testing.expectFiresTyped(check, R,
        \\const Wrapped = struct { values: [1]*u8 };
        \\fn forward(value: Wrapped) [1]*u8 { return value.values; }
        \\fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    return forward(.{ .values = .{&local} })[0];
        \\}
    );
}

test "selected returned field array retains element storage" {
    try testing.expectFiresTyped(check, R,
        \\const Wrapped = struct { nested: struct { values: [1]*u8 }, count: u8 };
        \\fn forward(value: [1]*u8) Wrapped {
        \\    return .{ .nested = .{ .values = value }, .count = 1 };
        \\}
        \\fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    return forward(.{&local}).nested.values[0];
        \\}
    );
}

test "selected independent field array ignores a borrowed sibling" {
    try testing.expectNoFireTyped(check,
        \\const Wrapped = struct { values: [1]*u8, borrowed: *u8 };
        \\fn forward(external: *u8, local: *u8) Wrapped {
        \\    return .{ .values = .{external}, .borrowed = local };
        \\}
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    return forward(external, &local).values[0];
        \\}
    );
}

test "owned pointer array result does not inherit argument storage" {
    try testing.expectNoFireTyped(check,
        \\var owned: u8 = 1;
        \\fn replace(_: [1]*u8) [1]*u8 { return .{&owned}; }
        \\fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    return replace(.{&local})[0];
        \\}
    );
}

test "fresh pointer array result does not inherit argument storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn replace(allocator: std.mem.Allocator, _: [1]*u8) ![1]*u8 {
        \\    return .{try allocator.create(u8)};
        \\}
        \\fn detect(allocator: std.mem.Allocator) !*u8 {
        \\    var local: u8 = 1;
        \\    return (try replace(allocator, .{&local}))[0];
        \\}
    );
}

test "unknown scalar array copier does not inherit argument storage" {
    try testing.expectNoFireTyped(check,
        \\fn detect(copy: *const fn (*u8) [1]u8) u8 {
        \\    var local: u8 = 1;
        \\    return copy(&local)[0];
        \\}
    );
}

test "pointer array element field selection excludes borrowed siblings" {
    try testing.expectNoFireTyped(check,
        \\const Pair = struct { selected: *u8, borrowed: *u8 };
        \\fn forward(values: [1]Pair) [1]Pair { return values; }
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    return forward(.{.{ .selected = external, .borrowed = &local }})[0].selected;
        \\}
    );
}

test "unknown pointer array constructor retains an actual array address" {
    try testing.expectFiresTyped(check, R,
        \\fn detect(wrap: *const fn (*[2]u8) [1]*[2]u8) *[2]u8 {
        \\    var local: [2]u8 = .{1, 2};
        \\    return wrap(&local)[0];
        \\}
    );
}

test "known pointer array alternative does not erase an unknown branch" {
    try testing.expectFiresTyped(check, R,
        \\fn choose(copy: *const fn ([1]*u8) [1]*u8, values: [1]*u8, external: *u8, condition: bool) [1]*u8 {
        \\    return if (condition) .{external} else copy(values);
        \\}
        \\fn detect(copy: *const fn ([1]*u8) [1]*u8, external: *u8, condition: bool) *u8 {
        \\    var local: u8 = 1;
        \\    return choose(copy, .{&local}, external, condition)[0];
        \\}
    );
}

test "forwarded field pointer array retains an addressed scalar field" {
    try testing.expectFiresTyped(check, R,
        \\const Wrapped = struct { values: [1]*u8 };
        \\fn forward(value: Wrapped) [1]*u8 { return value.values; }
        \\fn detect() *u8 {
        \\    var local = struct { value: u8 }{ .value = 1 };
        \\    return forward(.{ .values = .{&local.value} })[0];
        \\}
    );
}

test "array result retains addressed element and direct pointer loans" {
    try testing.expectFiresTyped(check, R,
        \\fn wrap(values: []u8) [1]*u8 { return .{&values[0]}; }
        \\pub fn detect() *u8 {
        \\    var local: [2]u8 = .{1, 2};
        \\    return wrap(&local)[0];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn wrap(value: *[2]u8) [1]*[2]u8 { return .{value}; }
        \\pub fn detect() *[2]u8 {
        \\    var local: [2]u8 = .{1, 2};
        \\    return wrap(&local)[0];
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn wrap(values: []u8) [1]*u8 { return .{&values[0]}; }
        \\pub fn detect(external: []u8) *u8 { return wrap(external)[0]; }
    );
    try testing.expectNoFireTyped(check,
        \\fn wrap(value: *[2]u8) [1]*[2]u8 { return .{value}; }
        \\pub fn detect(external: *[2]u8) *[2]u8 { return wrap(external)[0]; }
    );
}

test "copied pointer array result carries payload without borrowing the outer array" {
    try testing.expectNoFireTyped(check,
        \\fn copy(values: [1]*[2]u8) [1]*[2]u8 { return values; }
        \\pub fn detect(external: *[2]u8) *[2]u8 {
        \\    var pointers: [1]*[2]u8 = .{external};
        \\    return copy(pointers)[0];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn copy(values: [1]*[2]u8) [1]*[2]u8 { return values; }
        \\pub fn detect() *[2]u8 {
        \\    var local: [2]u8 = .{1, 2};
        \\    var pointers: [1]*[2]u8 = .{&local};
        \\    return copy(pointers)[0];
        \\}
    );
}

test "cast selected pointer load follows actual payload not outer cell" {
    try testing.expectFiresTyped(check, R,
        \\fn read(values: []*u8) *u8 { return values[0]; }
        \\pub fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{&local};
        \\    return read(@as([]*u8, &pointers));
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn read(values: []*u8) *u8 { return values[0]; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var pointers: [1]*u8 = .{external};
        \\    return read(@as([]*u8, &pointers));
        \\}
    );
}

test "borrowed array alias observes stores at final load" {
    try testing.expectFiresTyped(check, R,
        \\fn loan(values: []*u8) []*u8 { return values; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    const view = loan(&pointers);
        \\    pointers[0] = &local;
        \\    return view[0];
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn loan(values: []*u8) []*u8 { return values; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var pointers: [1]*u8 = .{external};
        \\    const view = loan(&pointers);
        \\    pointers[0] = external;
        \\    return view[0];
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    const snapshot = pointers;
        \\    pointers[0] = &local;
        \\    return snapshot[0];
        \\}
    );
}

test "pointer cell alias observes stores at final load" {
    try testing.expectFiresTyped(check, R,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    pointer = &local;
        \\    return read(cell);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    pointer = external;
        \\    return read(cell);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = external;
        \\    const snapshot = pointer;
        \\    pointer = &local;
        \\    return snapshot;
        \\}
    );
}

test "array element field stores preserve selected payload and siblings" {
    try testing.expectFiresTyped(check, R,
        \\const Pair = struct { selected: *u8, sibling: *u8 };
        \\fn loan(values: []Pair) []Pair { return values; }
        \\pub fn detect(external: *u8, index: usize) *u8 {
        \\    var local: u8 = 1;
        \\    var pairs: [1]Pair = .{.{.selected=external, .sibling=external}};
        \\    pairs[index].selected = &local;
        \\    return loan(&pairs)[0].selected;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Pair = struct { selected: *u8 };
        \\fn loan(values: []Pair) []Pair { return values; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pairs: [1]Pair = .{.{.selected=external}};
        \\    pairs[0].selected = &local;
        \\    return loan(&pairs)[0].selected;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Pair = struct { selected: *u8, sibling: *u8 };
        \\fn loan(values: []Pair) []Pair { return values; }
        \\pub fn detect(external: *u8, index: usize) *u8 {
        \\    var local: u8 = 1;
        \\    var pairs: [1]Pair = .{.{.selected=external, .sibling=external}};
        \\    pairs[index].sibling = &local;
        \\    pairs[0].selected = external;
        \\    return loan(&pairs)[0].selected;
        \\}
    );
}

test "subslice aliases retain external backing storage not local headers" {
    try testing.expectNoFireTyped(check,
        \\pub fn detect(external: []const u8) []const u8 {
        \\    const rest = external[1..];
        \\    return rest[0..1];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn detect() []const u8 {
        \\    var local: [2]u8 = .{1, 2};
        \\    const rest = local[0..];
        \\    return rest[0..1];
        \\}
    );
}

test "addressed pointee fields do not address local pointer headers" {
    try testing.expectNoFireTyped(check,
        \\const Entry = struct { value: u8 };
        \\pub fn detect(external: *Entry) *u8 {
        \\    const entry = external;
        \\    return &entry.value;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Entry = struct { value: u8 };
        \\pub fn detect() *u8 {
        \\    var entry = Entry{ .value = 1 };
        \\    return &entry.value;
        \\}
    );
}

test "array pointer loan preserves external aliases" {
    try testing.expectNoFireTyped(check,
        \\fn wrap(values: []u8) [1]*u8 { return .{&values[0]}; }
        \\pub fn detect(external: []u8) *u8 {
        \\    const alias = external;
        \\    return wrap(alias)[0];
        \\}
    );
}

test "copied array call result freezes payload before later source writes" {
    try testing.expectNoFireTyped(check,
        \\fn copy(values: [1]*u8) [1]*u8 { return values; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    const snapshot = copy(pointers);
        \\    pointers[0] = &local;
        \\    return snapshot[0];
        \\}
    );
}

test "direct slice alias and nested pointer cell alias observe late stores" {
    try testing.expectFiresTyped(check, R,
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    const view = pointers[0..];
        \\    const alias = view;
        \\    pointers[0] = &local;
        \\    return alias[0];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    const alias = cell;
        \\    pointer = &local;
        \\    return read(alias);
        \\}
    );
}

test "direct pointer cell load observes late payload without escaping cell" {
    try testing.expectFiresTyped(check, R,
        \\pub fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    pointer = &local;
        \\    return cell.*;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn detect(external: *u8) *u8 {
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    return cell.*;
        \\}
    );
}

test "selected channel independence retains storage written through an external receiver" {
    try testing.expectFiresTyped(check, R,
        \\const Model = struct {
        \\    bytes: []const u8,
        \\    fn get(self: *Model, input: []const u8) *Model { _ = input.len; return self; }
        \\};
        \\fn detect(model: *Model) *Model {
        \\    var input: [2]u8 = .{1, 2};
        \\    model.bytes = &input;
        \\    return model.get(&input);
        \\}
    );
}

test "direct formal loads retain stores through immutable pointer cell aliases" {
    try testing.expectFiresTyped(check, R,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    cell.* = &local;
        \\    return read(cell);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\fn detect(external: *u8) *u8 {
        \\    var pointer = external;
        \\    const cell = &pointer;
        \\    cell.* = external;
        \\    return read(cell);
        \\}
    );
}

test "direct formal loads join prior iteration pointer stores" {
    try testing.expectFiresTyped(check, R,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointer = external;
        \\    var i: usize = 0;
        \\    while (i < 2) : (i += 1) {
        \\        if (i == 1) return read(&pointer);
        \\        pointer = &local;
        \\    }
        \\    return external;
        \\}
    );
}

test "formal aggregate allocator fields cannot bypass actual stack provider requirements" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Source = struct { allocator: std.mem.Allocator };
        \\fn allocated(source: Source, n: usize) ![]u8 { return try source.allocator.alloc(u8, n); }
        \\fn detect() ![]u8 {
        \\    var backing: [32]u8 = undefined;
        \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
        \\    const source: Source = .{ .allocator = fixed.allocator() };
        \\    return allocated(source, 8);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Context = struct { allocator: std.mem.Allocator };
        \\fn copy(a: std.mem.Allocator, input: []const u8) ![]u8 { return a.dupe(u8, input); }
        \\fn detect(ctx: *Context) ![]u8 {
        \\    var backing: [128]u8 = undefined;
        \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
        \\    const alias = ctx;
        \\    alias.allocator = fixed.allocator();
        \\    return copy(ctx.allocator, "x");
        \\}
    );
}

test "selected element loads retain writes through const slice aliases" {
    try testing.expectFiresTyped(check, R,
        \\fn loan(values: []*u8) []*u8 { return values; }
        \\fn detect(external: *u8) *u8 {
        \\    var local: u8 = 1;
        \\    var pointers: [1]*u8 = .{external};
        \\    const view = pointers[0..];
        \\    view[0] = &local;
        \\    return loan(&pointers)[0];
        \\}
    );
}

test "external pointer and slice payloads observe current invocation stores" {
    try testing.expectFiresTyped(check, R,
        \\fn read(value: **u8) *u8 { return value.*; }
        \\fn detect(cell: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    cell.* = &local;
        \\    return read(cell);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn loan(values: []*u8) []*u8 { return values; }
        \\fn detect(values: []*u8) *u8 {
        \\    var local: u8 = 1;
        \\    values[0] = &local;
        \\    return loan(values)[0];
        \\}
    );
}

test "selected formal nonretention does not hide assembly outward stores" {
    try testing.expectFiresTyped(check, R,
        \\var saved: [*]const u8 = undefined;
        \\fn capture(input: []const u8) void {
        \\    asm volatile ("movq %[src], %[dst]"
        \\        : [dst] "=m" (saved)
        \\        : [src] "r" (input.ptr)
        \\    );
        \\}
        \\fn readBack() []const u8 { return saved[0..1]; }
        \\fn forward(input: []const u8) []const u8 { capture(input); return readBack(); }
        \\fn detect() []const u8 {
        \\    var bytes: [1]u8 = .{1};
        \\    return forward(&bytes);
        \\}
    );
}

test "selected field capture pointer loads retain late output pointee writes" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct { pointer: **u8 };
        \\fn detect(out: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    var state: State = .{ .pointer = out };
        \\    state.pointer = out;
        \\    const values = [_]**u8{state.pointer};
        \\    for (values) |item| {
        \\        out.* = &local;
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
    );
}

test "selected field capture pointer copies ignore later source field rebinding" {
    try testing.expectNoFireTyped(check,
        \\const State = struct { pointer: **u8 };
        \\fn detect(incoming: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    var header: *u8 = &local;
        \\    var state: State = .{ .pointer = incoming };
        \\    state.pointer = incoming;
        \\    const values = [_]**u8{state.pointer};
        \\    state.pointer = &header;
        \\    for (values) |item| {
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
    );
}

test "global inline pointer field aliases retain current invocation pointee stores" {
    try testing.expectFiresTyped(check, R,
        \\const Holder = struct { pointer: *u8 };
        \\var other: Holder = .{ .pointer = undefined };
        \\const saved: **u8 = &other.pointer;
        \\fn detect() *u8 {
        \\    var local: u8 = 1;
        \\    other.pointer = &local;
        \\    return saved.*;
        \\}
    );
}

test "address-free foreign numeric results do not carry frame storage" {
    try testing.expectNoFireTyped(check,
        \\extern "c" fn fill(out: *f64) c_int;
        \\const Result = struct { value: f64, ok: bool };
        \\pub fn sample() Result {
        \\    var value: f64 = undefined;
        \\    if (fill(&value) == 0) return .{ .value = 0, .ok = false };
        \\    return .{ .value = value, .ok = true };
        \\}
    );
}

test "address-free digest checksum and union results do not carry frame storage" {
    try testing.expectNoFireTyped(check,
        \\extern "c" fn digest(out: *[32]u8) void;
        \\pub fn sample() [32]u8 {
        \\    var bytes: [32]u8 = undefined;
        \\    digest(&bytes);
        \\    return bytes;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\extern "c" fn checksum(input: *[32]u8) u64;
        \\pub fn sample() u64 {
        \\    var bytes: [32]u8 = undefined;
        \\    return checksum(&bytes);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const Result = union(enum) { integer: u64, real: f64 };
        \\extern "c" fn fill(out: *Result) void;
        \\pub fn sample() Result {
        \\    var result: Result = undefined;
        \\    fill(&result);
        \\    return result;
        \\}
    );
}

test "numeric carrier with a borrowed sibling still carries frame storage" {
    try testing.expectFiresTyped(check, R,
        \\const Result = struct { value: f64, ok: bool, bytes: []const u8 };
        \\pub fn sample() Result {
        \\    var bytes: [32]u8 = undefined;
        \\    return .{ .value = 0, .ok = true, .bytes = bytes[0..] };
        \\}
    );
}

test "allocator duplicate of scratch returns an owned copy" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn sample(gpa: std.mem.Allocator) ![]u8 {
        \\    var scratch: [32]u8 = undefined;
        \\    return gpa.dupe(u8, scratch[0..]);
        \\}
    );
}

test "caller-owned buffer view does not borrow the current frame" {
    try testing.expectNoFireTyped(check,
        \\fn parse(input: []u8) []u8 { return input[1..]; }
        \\pub fn sample(out: *[32]u8) []u8 {
        \\    out[0] = 1;
        \\    return parse(out[0..]);
        \\}
    );
}

test "scratch view without an owned copy still borrows the current frame" {
    try testing.expectFiresTyped(check, R,
        \\fn parse(input: []u8) []u8 { return input[1..]; }
        \\pub fn sample() []u8 {
        \\    var scratch: [32]u8 = undefined;
        \\    return parse(scratch[0..]);
        \\}
    );
}

test "per-type container variables have static storage" {
    try testing.expectNoFireTyped(check,
        \\fn marker(comptime T: type) *const u8 {
        \\    const PerType = struct { const Ty = T; var byte: u8 = 0; };
        \\    return &PerType.byte;
        \\}
        \\pub fn sample() *const u8 { return marker(u32); }
    );
    try testing.expectNoFireTyped(check,
        \\fn marker(comptime T: type) []u8 {
        \\    const PerType = struct { const Ty = T; var bytes: [2]u8 = .{0, 0}; };
        \\    return PerType.bytes[0..];
        \\}
        \\pub fn sample() []u8 { return marker(u32); }
    );
    try testing.expectNoFireTyped(check,
        \\fn marker(comptime T: type) *const u8 {
        \\    const PerType = struct { const Ty = T; var byte: u8 = 0; };
        \\    const pointer = &PerType.byte;
        \\    return pointer;
        \\}
        \\pub fn sample() *const u8 { return marker(u32); }
    );
}

test "runtime array next to per-type storage remains frame storage" {
    try testing.expectFiresTyped(check, R,
        \\pub fn sample(comptime T: type) []u8 {
        \\    const PerType = struct { const Ty = T; var byte: u8 = 0; };
        \\    var bytes: [2]u8 = .{PerType.byte, 0};
        \\    return bytes[0..];
        \\}
    );
}

test "static type aliases do not become runtime frame cells" {
    try testing.expectNoFireTyped(check,
        \\pub fn sample() []u8 {
        \\    const Storage = struct { var bytes: [2]u8 = .{0, 0}; };
        \\    const Alias = Storage;
        \\    return Alias.bytes[0..];
        \\}
    );
}

test "runtime array values are not their normalized type values" {
    try testing.expectFiresTyped(check, R,
        \\pub fn sample() []u8 {
        \\    var bytes: [2]u8 = .{0, 0};
        \\    const alias = bytes[0..];
        \\    return alias;
        \\}
    );
}
