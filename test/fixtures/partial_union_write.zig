// oven-sh/bun#29422 — partial-union-write across all 4 site shapes, plus
// the tagged-union-payload-early-exit pair: the same partial retag reports
// when the union is the caller's, and stays quiet when the failing path
// only releases the storage raw.

const std = @import("std");

// ─── Site 1: `this.* = .{ .tag = try ... }` (Decompressor.zig)

const Reader = struct {
    pub fn deinit(_: *Reader, _: std.mem.Allocator) void {}
};

const Decompressor = union(enum) {
    none,
    zlib: *Reader,

    fn init(this: *Decompressor) !void {
        if (this.* == .none) {
            // BUG: tag is written first; if the try fails, this.* is
            // left as .{ .zlib = <garbage> } and a later deinit
            // dereferences the wild pointer.
            this.* = .{ .zlib = try ZlibInit() };
        }
    }
};

fn ZlibInit() !*Reader {
    return error.Failed;
}

// ─── Site 2: `this.* = .{ .Tag = .{ ... try ... } }` (Body.zig)
//             nested struct literal with the try buried inside.

const ReadableStream = struct {
    fn fromJS(_: usize) !?ReadableStream {
        return error.Failed;
    }
};

const Strong = struct {
    inner: ReadableStream,
    fn init(s: ReadableStream, _: usize) Strong {
        return .{ .inner = s };
    }
};

const Value = union(enum) {
    Empty,
    Locked: struct { readable: Strong, global: usize },

    fn bodify(this: *Value, value: usize, globalThis: usize) !void {
        // BUG: same as site 1 but the try is nested inside an inner
        // struct literal.  Token-scan still catches it.
        this.* = .{
            .Locked = .{
                .readable = Strong.init((try ReadableStream.fromJS(value)).?, globalThis),
                .global = globalThis,
            },
        };
    }
};

// ─── Site 3: `this.field = .{ .tag = ... catch return ... }` (Listener.zig)
//             catch-tail return.

const NamedPipe = struct { handle: usize };

const Listener = struct {
    listener: union(enum) {
        none,
        namedPipe: NamedPipe,
    },

    fn listen(this: *Listener) usize {
        // BUG: this.listener gets tag .namedPipe with stale payload
        // if listenPipe errors.
        this.listener = .{
            .namedPipe = listenPipe() catch return 0,
        };
        return 1;
    }
};

fn listenPipe() !NamedPipe {
    return error.Failed;
}

// ─── Site 4: `obj.field = .{ .tag = ... catch |err| switch ... return ... }` (JSBundler.zig)
//             catch with capture, switch arm returns.

const Msg = struct {
    text: []const u8,
    fn fromJS(_: usize) !Msg {
        return error.Failed;
    }
};

const Resolve = struct {
    value: union(enum) {
        pending,
        err: Msg,
    },

    fn onError(resolve: *Resolve, exception: usize) void {
        // BUG: tag is .err with garbage Msg bytes on the JSError arm.
        resolve.value = .{
            .err = Msg.fromJS(exception) catch |err| switch (err) {
                error.Failed => {
                    return;
                },
            },
        };
    }
};

// ─── Control 1: pure-local var.  NOT dangerous (frame dies on return).

fn localVar() !void {
    var x: Decompressor = .none;
    x = .{ .zlib = try ZlibInit() };
}

// ─── Control 2: payload is plain, no try/catch-return.  Not dangerous.

fn plainPayload(this: *Decompressor, r: *Reader) void {
    this.* = .{ .zlib = r };
}

// ─── Control 3: catch with value, no return / unreachable.
//                Should NOT fire (catch produces a fallback value).

fn defaultReader() *Reader {
    return undefined;
}

fn catchValue(this: *Decompressor) void {
    this.* = .{ .zlib = ZlibInit() catch defaultReader() };
}

// ─── Site 5: caller-visible union field with a `try` payload.
//             `resolve` is a parameter, so the union lives in storage
//             the caller owns and can read on the error path.  The
//             `.err` tag is written before `Msg.fromJS` resolves, so a
//             failed call leaves `.err` active over `.pending`'s
//             payload bytes.

fn onTry(resolve: *Resolve, exception: usize) !void {
    resolve.value = .{ .err = try Msg.fromJS(exception) };
}

// ─── Control 4: private union storage whose only cleanup is a raw
//                `free` of the whole slice.  Every failing path
//                releases the allocation without reading the union
//                element, so the partial retag is unobservable.

fn privateBuild(gpa: std.mem.Allocator) !void {
    const fields = try gpa.alloc(Decompressor, 1);
    defer gpa.free(fields);
    fields[0] = .{ .zlib = try ZlibInit() };
}

// ─── Control 5: the same retag as site 5, into frame-private storage.
//                `pending` never leaves this frame, and the `defer`
//                releases the whole slice without reading the union
//                element, so nothing can observe the half-retagged
//                `.err` over `.pending`'s payload bytes.  Only storage
//                ownership differs from site 5 — same union, same field,
//                same `Msg.fromJS` call, same `try`.

fn privateRetag(gpa: std.mem.Allocator, exception: usize) !void {
    const fields = try gpa.alloc(Resolve, 1);
    defer gpa.free(fields);
    var pending: Resolve = .{ .value = .pending };
    pending.value = .{ .err = try Msg.fromJS(exception) };
    fields[0] = pending;
}
