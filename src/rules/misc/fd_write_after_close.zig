//! File-descriptor use-after-close detector — `const <X> = try
//! <dir>.<open-method>(...);` binds an OS file handle; `<X>.close();`
//! invalidates it; any subsequent `<X>.<io-method>(...)` /
//! `<X>.<field-access>` reads or writes through a dangling handle.
//!
//! Rewritten via the query DSL: the rule is now a declarative
//! description of three patterns + scope constraints, NOT a
//! hand-rolled token walker.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const trace = @import("../../trace.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Atom = query.Atom;
const R = "fd-write-after-close";

// Pattern: `const $X = [try] <ident>.<openMethod>(...);`
//   slot 0 — bound name X
const open_call = &[_]Atom{
    .{ .tok = .keyword_const },
    .{ .capture = 0 },
    .{ .tok = .equal },
    .{ .opt = &[_]Atom{.{ .tok = .keyword_try }} },
    .{ .tok = .identifier }, // receiver (dir / sock / etc.)
    .{ .tok = .period },
    .{ .pred = isOpenerMethod },
    .paren_args,
};

// Pattern: `$X.close()` — inline close, same scope.
const close_call = &[_]Atom{
    .{ .ref = 0 },
    .{ .tok = .period },
    .{ .text = "close" },
    .paren_args,
};

// Pattern: any reference to $X — used to detect "use after close"
// inside the enclosing scope.
const use_of_x = &[_]Atom{.{ .ref = 0 }};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    if (!config_mod.isEnabled(config, .fd_write_after_close)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    const binds = try query.findAllInBody(gpa, tree, open_call, first, last);
    defer gpa.free(binds);

    for (binds) |b| {
        trace.note(R, tree, b.captures[0].?, "bound file handle via opener");
        const close = query.findInSameScope(tree, close_call, b.end + 1, last, &b) orelse {
            trace.skip(R, tree, b.captures[0].?, "no inline .close() at same depth (defer/errdefer is fine)");
            continue;
        };
        const use = query.findInEnclosingScope(tree, use_of_x, close.end + 1, last, &b) orelse {
            trace.skip(R, tree, close.start, "close found but no later use of binding in enclosing scope");
            continue;
        };
        trace.match(R, tree, use.start, "use after close");
        try report(gpa, problems, tree, b.captures[0].?, use.start);
    }
}

fn isOpenerMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "createFile") or
        std.mem.eql(u8, name, "createFileZ") or
        std.mem.eql(u8, name, "openFile") or
        std.mem.eql(u8, name, "openFileZ") or
        std.mem.eql(u8, name, "openDir") or
        std.mem.eql(u8, name, "openDirZ") or
        std.mem.eql(u8, name, "open") or
        std.mem.eql(u8, name, "openZ") or
        std.mem.eql(u8, name, "openat") or
        std.mem.eql(u8, name, "openatZ") or
        std.mem.eql(u8, name, "accept") or
        std.mem.eql(u8, name, "socket");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(problem.Problem),
    tree: *const Ast,
    bind_tok: query.TokenIndex,
    use_tok: query.TokenIndex,
) !void {
    const x_name = tree.tokenSlice(bind_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "use of `{s}` after `{s}.close()` — the file handle is invalid; subsequent operations through `{s}` read/write through a dangling fd (fd-reuse on POSIX) or a closed handle (Windows)",
        .{ x_name, x_name, x_name },
    );
    errdefer gpa.free(msg);

    const note_label = try std.fmt.allocPrint(gpa, "file handle opened here", .{});
    errdefer gpa.free(note_label);

    var notes = try gpa.alloc(problem.Note, 1);
    errdefer gpa.free(notes);
    notes[0] = .{
        .start = try problem.Pos.fromTokenStart(tree, bind_tok),
        .end = try problem.Pos.fromTokenEnd(tree, bind_tok),
        .label = note_label,
    };

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try problem.Pos.fromTokenStart(tree, use_tok),
        .end = try problem.Pos.fromTokenEnd(tree, use_tok),
        .message = msg,
        .notes = notes,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "createFile then close then writeAll fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\pub fn buggy(dir: std.fs.Dir) !void {
        \\    const file = try dir.createFile("x", .{});
        \\    file.close();
        \\    try file.writeAll("hi");
        \\}
    );
}

test "defer close doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(dir: std.fs.Dir) !void {
        \\    const file = try dir.createFile("x", .{});
        \\    defer file.close();
        \\    try file.writeAll("hi");
        \\}
    );
}

test "errdefer close also skipped" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(dir: std.fs.Dir) !void {
        \\    const file = try dir.createFile("x", .{});
        \\    errdefer file.close();
        \\    try file.writeAll("hi");
        \\    file.close();
        \\}
    );
}

test "close inside catch block (diverges) is skipped" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(dir: std.fs.Dir) !void {
        \\    const file = try dir.createFile("x", .{});
        \\    file.writeAll("a") catch {
        \\        file.close();
        \\        return;
        \\    };
        \\    try file.writeAll("b");
        \\}
    );
}

test "openFile variant caught" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\pub fn buggy(dir: std.fs.Dir) !void {
        \\    const file = try dir.openFile("x", .{});
        \\    file.close();
        \\    _ = try file.read(undefined);
        \\}
    );
}

test "field access (file.handle) after close fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\pub fn buggy(dir: std.fs.Dir) !void {
        \\    const file = try dir.createFile("x", .{});
        \\    file.close();
        \\    const h = file.handle;
        \\    _ = h;
        \\}
    );
}

test "shadowed name in sibling scope doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(dir: std.fs.Dir, files: []std.fs.File) !void {
        \\    {
        \\        const file = try dir.createFile("x", .{});
        \\        file.close();
        \\    }
        \\    for (files) |file| {
        \\        _ = file;
        \\    }
        \\}
    );
}
