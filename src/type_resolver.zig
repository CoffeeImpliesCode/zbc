//! Bridge between zbc and the type engine.
//! Re-exports TypeContext + TypeResolver for use by lib.zig / main.zig,
//! and Toolchain alongside them: a run discovers the compiler once and
//! lends that answer to every context it opens, instead of each context
//! paying its own `zig env`.

const engine = @import("type_engine");

pub const TypeContext = engine.TypeContext;
pub const TypeResolver = engine.TypeResolver;
pub const Toolchain = engine.Toolchain;

/// Owns a TypeContext that may or may not be initialized.
/// Eliminates the `var ok = false; defer if (ok) x.deinit()` pattern.
pub const ManagedContext = struct {
    inner: TypeContext = undefined,
    initialized: bool = false,

    pub fn tryInit(self: *ManagedContext, gpa: std.mem.Allocator, io: std.Io) void {
        self.inner.init(gpa, io) catch return;
        self.initialized = true;
    }

    pub fn get(self: *ManagedContext) ?*TypeContext {
        return if (self.initialized) &self.inner else null;
    }

    pub fn deinit(self: *ManagedContext) void {
        if (self.initialized) self.inner.deinit();
    }
};

/// Owns a TypeResolver that may or may not be initialized.
pub const ManagedResolver = struct {
    inner: TypeResolver = undefined,
    initialized: bool = false,

    pub fn tryInit(
        self: *ManagedResolver,
        ctx: *TypeContext,
        gpa: std.mem.Allocator,
        path: []const u8,
        src: [:0]const u8,
    ) void {
        self.inner.init(ctx, gpa, path, src) catch return;
        self.initialized = true;
    }

    pub fn get(self: *ManagedResolver) ?*TypeResolver {
        return if (self.initialized) &self.inner else null;
    }

    pub fn deinit(self: *ManagedResolver) void {
        if (self.initialized) self.inner.deinit();
    }
};

const std = @import("std");
