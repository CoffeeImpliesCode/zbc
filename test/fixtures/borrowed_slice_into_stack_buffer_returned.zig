// borrowed-slice-into-stack-buffer-returned — ziglang/zig#25713
// class.  Parser populates result with slices INTO a stack
// buffer; returning the result leaves caller with dangling
// sub-slices.

const std = @import("std");

const SemanticVersion = struct {
    major: u32 = 0,
    minor: u32 = 0,
    patch: u32 = 0,
    pre: ?[]const u8 = null,
    build: ?[]const u8 = null,

    pub fn parse(input: []const u8) SemanticVersion {
        return .{ .pre = input };
    }
};

// Bug — fires on the `return ver`.
pub fn detectBuggy() SemanticVersion {
    var buf: [64]u8 = [_]u8{0} ** 64;
    const ver = SemanticVersion.parse(&buf);
    return ver;
}

// Control — overwrite every borrowing field before return. Should NOT fire:
// both pre and build are null, so no stack-backed slice remains in stripped.
pub fn detectFixed() SemanticVersion {
    var buf: [64]u8 = [_]u8{0} ** 64;
    const ver = SemanticVersion.parse(&buf);
    var stripped = ver;
    stripped.pre = null;
    stripped.build = null;
    return stripped;
}
