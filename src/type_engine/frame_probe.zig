//! THROWAWAY DIAGNOSTIC — NOT PART OF THE PRODUCT BUILD, DELETE AFTER TRACING.
//!
//! Nothing imports this file, so the product's sources are untouched by its
//! presence.  It exists so the engine's borrowed-generic-frame query path can
//! be OBSERVED step by step instead of aborting on the first null: the engine
//! test reaches `frame.intInfo(field).?`, which aborts the whole run at the
//! first unanswered step and tells us nothing about which step that was.
//!
//! It prints, it asserts nothing, and it never substitutes a value for a null.
//!
//! Run:  zig run src/type_engine/frame_probe.zig
//! (from the repository root, with the pinned toolchain)
//!
//! WHAT EACH LINE MEANS
//!
//!   container      what resolving the `wide`/`narrow` PARAMETER produces — the
//!                   container the engine's frameForContainer is handed.
//!   bound_params   the map that container carries.  If `T` is not in here, the
//!                   substitution can never happen and the null is upstream.
//!   bound token    each entry's token text, is_type_val and interned index, so
//!                   the KEY IDENTITY is visible and not inferred.
//!   T              the formal identifier read in that frame.
//!   self           the receiver identifier read in that frame.
//!   self.value     the whole field access, i.e. exactly what the engine asks.
//!   field unframed the field declaration resolved with no container.
//!   field framed   the same declaration resolved under the declaring container,
//!                   i.e. whether `inContainer` changes anything here.
//!
//! `NULL` means the analyser genuinely answered unknown at that step.  No step
//! invents, defaults, or falls back.

const std = @import("std");
const analysis = @import("analysis.zig");
const DocumentStore = @import("document_store.zig");
const InternPool = @import("intern_pool.zig");
const Uri = @import("uri.zig");

const Type = analysis.Type;
const Ast = std.zig.Ast;

/// The engine's fixture, verbatim.  `missing()` is undeclared on purpose: the
/// parser does not resolve identifiers, so this parses and runs, and keeping
/// the declaration means the traced AST is the one the engine test really uses.
const fixture_source: [:0]const u8 =
    \\fn Box(comptime T: type) type {
    \\    return struct {
    \\        value: T,
    \\        fn read(self: *const @This()) T { return self.value; }
    \\        fn unknown() void { missing(); }
    \\    };
    \\}
    \\fn use(wide: Box(u64), narrow: Box(u8)) void { _ = wide; _ = narrow; }
;

fn say(label: []const u8, maybe: ?Type) void {
    const t = maybe orelse {
        std.debug.print("PROBE {s}: NULL\n", .{label});
        return;
    };
    std.debug.print("PROBE {s}: is_type_val={any} data={any} ipIndex={any}\n", .{
        label,
        t.is_type_val,
        @as([]const u8, @tagName(t.data)),
        t.ipIndex(),
    });
}

/// The first `.identifier` node in `tree` spelling `name`.
fn findIdentifier(tree: *const Ast, name: []const u8) ?Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .identifier) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) return node;
    }
    return null;
}

/// The `self.value` field access and its receiver, found by field name so the
/// probe does not depend on node order.
const FieldAccess = struct { node: Ast.Node.Index, receiver: Ast.Node.Index };

fn findFieldAccess(tree: *const Ast, field: []const u8) ?FieldAccess {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const lhs, const name_token = tree.nodeData(node).node_and_token;
        if (std.mem.eql(u8, tree.tokenSlice(name_token), field)) {
            return .{ .node = node, .receiver = lhs };
        }
    }
    return null;
}

/// Print a container's binding identity: whether it binds anything, WHICH
/// scope it belongs to, and every bound token.  Two containers can be the
/// same kind of thing and still differ exactly here, which is what the
/// `equals_frame=false` observation needs resolved.
fn describeContainer(label: []const u8, ty: Type, tree: *const Ast) void {
    if (ty.data != .container) {
        std.debug.print("PROBE {s}: NOT A CONTAINER data={any} is_type_val={any}\n", .{
            label,
            @as([]const u8, @tagName(ty.data)),
            ty.is_type_val,
        });
        return;
    }
    const info = ty.data.container;
    // `doc` is the declaring document, so "same document or not" is a
    // direct A/B in one line rather than an argument.
    std.debug.print("PROBE {s}: is_type_val={any} bound_params={any} scope_is_root={any} scope={any} doc={any}\n", .{
        label,
        ty.is_type_val,
        info.bound_params.count(),
        info.scope_handle.scope == .root,
        info.scope_handle.scope,
        info.scope_handle.handle.document.uri.raw,
    });
    for (info.bound_params.keys(), info.bound_params.values()) |k, v| {
        std.debug.print("PROBE {s}: bound token={any} is_type_val={any} ipIndex={any}\n", .{
            label,
            tree.tokenSlice(k.token),
            v.is_type_val,
            v.ipIndex(),
        });
    }
}

pub fn main(init: std.process.Init) void {
    run(init) catch |err| {
        std.debug.print("FAIL frame-probe: {s}\n", .{@errorName(err)});
        std.process.exit(2);
    };
}

fn run(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;

    var arena: std.heap.ArenaAllocator = .init(gpa);
    defer arena.deinit();

    var environ_map: std.process.Environ.Map = .init(gpa);
    defer environ_map.deinit();

    var diagnostics: @import("diagnostics_collection.zig") = .{ .io = io, .allocator = gpa };

    var modules: DocumentStore.ModuleRegistry = .init(gpa);
    defer modules.deinit();

    var ip: InternPool = try InternPool.init(io, gpa);
    defer ip.deinit(gpa);

    // Only a canonical absolute name is needed; the document is opened from
    // the text below, never read off the filesystem.
    var cwd_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const cwd_len = try std.Io.Dir.cwd().realPathFile(io, ".", &cwd_buffer);
    const path = try std.fs.path.join(gpa, &.{ cwd_buffer[0..cwd_len], "probe_frame.zig" });
    defer gpa.free(path);
    const uri = try Uri.fromPath(arena.allocator(), path);

    var store: DocumentStore = .{
        .io = io,
        .allocator = gpa,
        .modules = &modules,
        .config = .{
            .environ_map = &environ_map,
            .zig_exe_path = null,
            .zig_lib_dir = null,
            .build_runner_path = null,
            .builtin_path = null,
            .global_cache_dir = null,
            .wasi_preopens = {},
        },
        .diagnostics_collection = &diagnostics,
    };
    defer store.deinit();

    try store.openLspSyncedDocument(uri, fixture_source);
    const handle = store.getHandle(uri, .unscoped) orelse return error.HandleMissing;
    const tree = &handle.document.tree;
    std.debug.print("PROBE parse_errors={any}\n", .{tree.errors.len});

    var analyser = analysis.init(gpa, arena.allocator(), &store, &ip, handle);
    defer analyser.deinit();

    const access = findFieldAccess(tree, "value") orelse return error.NoFieldAccess;
    const formal_t = findIdentifier(tree, "T") orelse return error.NoFormal;
    const receiver = access.receiver;

    for ([_][]const u8{ "wide", "narrow" }) |name| {
        std.debug.print("PROBE === {s} ===\n", .{name});

        const id_node = findIdentifier(tree, name) orelse return error.NoParam;
        const id_token = tree.nodeMainToken(id_node);
        const decl = (try analyser.lookupSymbolGlobal(handle, name, tree.tokenStart(id_token))) orelse
            return error.NoParamDecl;
        const maybe_frame = try decl.resolveType(&analyser);
        say("container", maybe_frame);

        const frame = maybe_frame orelse continue;
        if (frame.data == .container) {
            const info = frame.data.container;
            std.debug.print("PROBE {s}: bound_params={any} scope_is_root={any}\n", .{
                name,
                info.bound_params.count(),
                info.scope_handle.scope == .root,
            });
            for (info.bound_params.keys(), info.bound_params.values()) |k, v| {
                std.debug.print("PROBE {s}: bound token={any} is_type_val={any} ipIndex={any}\n", .{
                    name,
                    tree.tokenSlice(k.token),
                    v.is_type_val,
                    v.ipIndex(),
                });
            }
        }

        say("  T", try analyser.resolveTypeOfNode(.{
            .node_handle = .of(formal_t, handle),
            .container_type = frame,
        }));
        say("  self", try analyser.resolveTypeOfNode(.{
            .node_handle = .of(receiver, handle),
            .container_type = frame,
        }));
        say("  self.value", try analyser.resolveTypeOfNode(.{
            .node_handle = .of(access.node, handle),
            .container_type = frame,
        }));

        // WHY `self.value` differs from `field unframed`: the field access
        // reads through the DEREFERENCED receiver, and `lookupSymbolContainer`
        // attaches whatever container it was handed.  Print that container,
        // whether it is a type value (which takes a DIFFERENT lookup branch),
        // and whether the lookup on it finds the field at all.
        if (try analyser.resolveTypeOfNode(.{
            .node_handle = .of(receiver, handle),
            .container_type = frame,
        })) |self_ty| {
            describeContainer("  frame", frame, tree);
            const left = (try analysis.resolveDerefType(&analyser, self_ty)) orelse self_ty;
            say("  left_type", left);
            describeContainer("  left", left, tree);
            if (try left.lookupSymbol(&analyser, "value")) |f| {
                std.debug.print("PROBE {s}: left lookup attached={any} equals_frame={any}\n", .{
                    name,
                    f.container_type != null,
                    (f.container_type orelse self_ty).eql(frame),
                });
                say("  via left lookup", try f.resolveType(&analyser));
            } else {
                std.debug.print("PROBE {s}: left lookup NULL\n", .{name});
            }
        }

        if (try frame.lookupSymbol(&analyser, "value")) |field| {
            // The container THAT lookup attached — the third of the three, so
            // frame, left_type and this can be compared side by side in one
            // block.  If `left_type` is the odd one out, the defect is
            // upstream of the field lookup and a field-access repair would be
            // a second wrong inference.
            describeContainer("  field.from_frame", field.container_type orelse frame, tree);
            say("  field unframed", try field.resolveType(&analyser));
            say("  field framed", try field.inContainer(frame).resolveType(&analyser));
        } else {
            std.debug.print("PROBE {s}: field lookup NULL\n", .{name});
        }
    }
}