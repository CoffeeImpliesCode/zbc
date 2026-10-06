//! Bridge between zbc and the type engine.
//! Re-exports TypeContext + TypeResolver for use by lib.zig / main.zig.

const engine = @import("type_engine");

pub const TypeContext = engine.TypeContext;
pub const TypeResolver = engine.TypeResolver;

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
