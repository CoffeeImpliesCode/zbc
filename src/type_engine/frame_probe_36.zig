//! THROWAWAY DIAGNOSTIC — NOT PART OF THE PRODUCT BUILD, DELETE AFTER TRACING.
//!
//! Sibling of frame_probe.zig.  Imports engine.zig READ-ONLY (no edit to it,
//! and nothing imports either probe).  Drives test 36's real failure path so
//! the MissingCallee is observed rather than inferred, and prints WHICH of
//! `reachedCallable`'s three null exits is taken.
//!
//! Run:  zig run src/type_engine/frame_probe_36.zig
//!
//! Prints nothing but facts and asserts nothing.

const std = @import("std");
const engine = @import("engine.zig");
const analysis = @import("analysis.zig");
const Ast = std.zig.Ast;

/// The engine's own fixture, copied verbatim from engine.zig:3175.  It is a
/// file-private const there, so it is reproduced here rather than imported.
const generic_context_fixture: [:0]const u8 =
    \\const Reading = struct {
    \\    total: u64,
    \\    pub fn read(self: *const Reading) u64 { return self.total; }
    \\    pub fn write(self: *Reading, value: u64) void { self.total = value; }
    \\};
    \\const Writing = struct {
    \\    slot: u8,
    \\    pub fn read(self: *const Writing) u8 { return self.slot; }
    \\    pub fn write(self: *Writing, value: u8) void { self.slot = value; }
    \\};
    \\fn Cache(comptime T: type, comptime Context: type) type {
    \\    return struct {
    \\        context: Context,
    \\        pub fn run(self: *@This(), item: T) T {
    \\            const seen = self.context.read();
    \\            self.context.write(item);
    \\            return seen;
    \\        }
    \\    };
    \\}
    \\fn useReading(cache: *Cache(u64, Reading)) u64 { return cache.run(1); }
    \\fn useWriting(cache: *Cache(u8, Writing)) u8 { return cache.run(1); }
;

fn say(label: []const u8, maybe: ?analysis.Type) void {
    const t = maybe orelse {
        std.debug.print("PROBE36 {s}: NULL\n", .{label});
        return;
    };
    std.debug.print("PROBE36 {s}: is_type_val={any} data={any} ipIndex={any}\n", .{
        label,
        t.is_type_val,
        @as([]const u8, @tagName(t.data)),
        t.ipIndex(),
    });
}

fn describeContainer(label: []const u8, ty: analysis.Type) void {
    if (ty.data != .container) {
        std.debug.print("PROBE36 {s}: NOT A CONTAINER data={any} is_type_val={any}\n", .{
            label,
            @as([]const u8, @tagName(ty.data)),
            ty.is_type_val,
        });
        return;
    }
    const info = ty.data.container;
    std.debug.print("PROBE36 {s}: is_type_val={any} bound_params={any} scope_is_root={any} scope={any} doc={any}\n", .{
        label,
        ty.is_type_val,
        info.bound_params.count(),
        info.scope_handle.scope == .root,
        info.scope_handle.scope,
        info.scope_handle.handle.document.uri.raw,
    });
}

/// Copied VERBATIM from engine.zig `testNthCallNamed`, including its
/// `else => continue` and its exact token selection.  The probe must drive
/// the same node the engine test drives; an argument that the two agree on
/// this fixture is worth less than the certainty, and `lastToken` is not
/// the same rule for every callee shape.
fn testNthCallNamed(tree: *const Ast, name: []const u8, occurrence: usize) !Ast.Node.Index {
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        const callee = call.ast.fn_expr;
        const written = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => continue,
        };
        if (!std.mem.eql(u8, tree.tokenSlice(written), name)) continue;
        if (seen == occurrence) return node;
        seen += 1;
    }
    return error.TestUnexpectedResult;
}

pub fn main(init: std.process.Init) void {
    run(init) catch |err| {
        std.debug.print("FAIL frame-probe-36: {s}\n", .{@errorName(err)});
        std.process.exit(2);
    };
}

fn run(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;

    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();

    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-generic-context-probe.zig", generic_context_fixture);
    defer resolver.deinit();

    const handle = resolver.handle;
    const tree = &handle.document.tree;
    std.debug.print("PROBE36 parse_errors={any}\n", .{tree.errors.len});

    const analyser = &resolver.analyser;

    for ([_]usize{ 0, 1 }) |nth| {
        const label: []const u8 = if (nth == 0) "wide" else "narrow";
        std.debug.print("PROBE36 === {s} ===\n", .{label});

        const call_node = try testNthCallNamed(tree, "run", nth);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, call_node).?;

        // What the engine saw, through its own public entry point.
        switch (try resolver.functionReferenceOfCall(call_node)) {
            .unknown => std.debug.print("PROBE36 {s}: functionReferenceOfCall=unknown\n", .{label}),
            .not_callable => std.debug.print("PROBE36 {s}: functionReferenceOfCall=not_callable\n", .{label}),
            .function => |reference| {
                std.debug.print("PROBE36 {s}: functionReferenceOfCall=function fn_token={any}\n", .{
                    label,
                    reference.fn_token,
                });
                say("  callee actual_type", reference.actual_type);
                describeContainer("  callee container", reference.actual_type);
            },
        }

        // Which of reachedCallable's three null exits is taken.  `options` is
        // reconstructed as the root frame the engine passes (container null);
        // if the engine's root frame carries a container this reconstruction
        // is itself a difference, and the receiver line below will show it.
        const options: analysis.ResolveOptions = .{
            .node_handle = .of(call.ast.fn_expr, handle),
            .container_type = null,
        };
        const raw = try analyser.resolveTypeOfNode(.of(call.ast.fn_expr, handle));
        const recv_node = tree.nodeData(call.ast.fn_expr).node_and_token[0];
        const recv_ty = try analyser.resolveTypeOfNode(.of(recv_node, handle));
        say("  receiver raw", recv_ty);
        if (recv_ty) |rt| {
            if (try analyser.resolveDerefType(rt)) |dt| {
                say("  receiver deref", dt);
                if (dt.data == .container) {
                    const info = dt.data.container;
                    std.debug.print("PROBE36 {s}: scope={any} uri={s}\n", .{ label, info.scope_handle.scope, info.scope_handle.handle.document.uri.raw });
                    const ds = try info.scope_handle.handle.getDocumentScope();
                    for (ds.getScopeDeclarationsConst(info.scope_handle.scope)) |decl_idx| {
                        const decl = ds.declarations.get(@intFromEnum(decl_idx));
                        const name = switch (decl) {
                            .ast_node => |n| tree.tokenSlice(tree.nodeMainToken(n)),
                            else => "?",
                        };
                        std.debug.print("PROBE36 {s}:   member {s}\n", .{ label, name });
                    }
                    inline for ([2]analysis.DocumentScope.DeclarationLookup.Kind{ .other, .field }) |kind| {
                        const hit = ds.getScopeDeclaration(.{ .scope = info.scope_handle.scope, .name = "run", .kind = kind });
                        std.debug.print("PROBE36 {s}: direct kind={any} hit={any}\n", .{ label, kind, hit != .none });
                    }
                }
                if (try analysis.lookupSymbolContainer(dt, "run", .other)) |decl| {
                    std.debug.print("PROBE36 {s}: container.other found\n", .{label});
                    if (try decl.resolveType(analyser)) |dt2| {
                        say("  run decl type", dt2);
                        if (try analyser.resolveFuncProtoOfCallable(dt2)) |proto| {
                            say("  run proto", proto);
                            const self_ty = try dt.typeOf(analyser);
                            say("  self.typeOf", self_ty);
                            const p0 = proto.data.function.parameters[0].type;
                            say("  proto param0", p0);
                            if (p0.data == .ip_index) {
                                std.debug.print("PROBE36 {s}: param0 ip.type={any} ip.index={any}\n", .{ label, p0.data.ip_index.type, p0.data.ip_index.index });
                                const tkey = analyser.ip.indexToKey(p0.data.ip_index.type);
                                std.debug.print("PROBE36 {s}: param0 typekey={s}\n", .{ label, @tagName(tkey) });
                            }
                            std.debug.print("PROBE36 {s}: firstParamIs={any}\n", .{ label, analyser.firstParamIs(proto, self_ty) });
                        } else {
                            std.debug.print("PROBE36 {s}: resolveFuncProtoOfCallable NULL\n", .{label});
                        }
                    } else {
                        std.debug.print("PROBE36 {s}: run decl resolveType NULL\n", .{label});
                    }
                } else {
                    std.debug.print("PROBE36 {s}: container.other NULL\n", .{label});
                }
            } else {
                std.debug.print("PROBE36 {s}: receiver deref NULL\n", .{label});
            }
        }

        const callable = if (raw) |r| try analyser.resolveFuncProtoOfCallable(r) else null;
        if (callable == null) {
            std.debug.print("PROBE36 {s}: EXIT=no-callable\n", .{label});
        } else if (callable.?.is_type_val) {
            std.debug.print("PROBE36 {s}: EXIT=is_type_val\n", .{label});
        } else if (callable.?.data.function.has_varargs) {
            std.debug.print("PROBE36 {s}: EXIT=has_varargs\n", .{label});
        } else {
            const receiver = try analyser.isInstanceCall(options, call, callable.?);
            const want = call.ast.params.len + @intFromBool(receiver);
            const have = callable.?.data.function.parameters.len;
            std.debug.print("PROBE36 {s}: EXIT=arity receiver={any} params={any} want={any} have={any}\n", .{
                label,
                receiver,
                call.ast.params.len,
                want,
                have,
            });
        }
    }
}