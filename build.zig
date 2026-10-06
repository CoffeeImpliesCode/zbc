//! zbc build — exposes the library module + builds the CLI exe.
//!
//! Consumers add zbc as a path dependency in their build.zig.zon
//! and then in their build.zig:
//!
//!     const zbc_dep = b.dependency("zbc", .{
//!         .target = target,
//!         .optimize = optimize,
//!     });
//!     exe.root_module.addImport("zbc", zbc_dep.module("zbc"));
//!
//! Then in their Zig code:
//!
//!     const zbc = @import("zbc");
//!     const problems = try zbc.analyzeEscape(gpa, io, path, &cache, &zbc.DefaultConfig);

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // ── Type engine module ──────────────────────────────────
    // Extracted ZLS type-resolution machinery, optimised for
    // repo-wide batch analysis.  No LSP server, no incremental
    // update protocol — just the type-resolution core.
    const engine_mod = b.addModule("type_engine", .{
        .root_source_file = b.path("src/type_engine/engine.zig"),
        .target = target,
        .optimize = optimize,
    });

    // ── Public library module ───────────────────────────────
    // Importable by downstream consumers as `@import("zbc")`.
    const lib_mod = b.addModule("zbc", .{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    lib_mod.addImport("type_engine", engine_mod);

    // ── CLI executable ──────────────────────────────────────
    // Standalone binary; useful for one-off sweeps without
    // integrating into a host build.zig.
    const exe_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    exe_mod.addImport("type_engine", engine_mod);
    const exe = b.addExecutable(.{
        .name = "zbc",
        .root_module = exe_mod,
    });

    exe_mod.link_libc = true; // project_cache.zig uses std.c.realpath on non-absolute paths
    b.installArtifact(exe);

    // ── Dogfood: self-check on every `zig build` ────────────
    const self_check = b.addRunArtifact(exe);
    self_check.addDirectoryArg(b.path("src/"));
    b.default_step.dependOn(&self_check.step);

    const run_cmd = b.addRunArtifact(exe);
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run zbc CLI");
    run_step.dependOn(&run_cmd.step);

    // ── Tests ───────────────────────────────────────────────
    const test_step = b.step("test", "Run zbc tests");

    // Library tests (lib.zig refAllDecls every submodule).
    lib_mod.link_libc = true; // project_cache.zig uses std.c.realpath
    const lib_tests = b.addTest(.{ .root_module = lib_mod });
    test_step.dependOn(&b.addRunArtifact(lib_tests).step);

    // CLI tests (argparse + invariant-list parsing).
    const cli_test_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    cli_test_mod.addImport("type_engine", engine_mod);
    cli_test_mod.link_libc = true; // transitively pulls in project_cache.zig
    const cli_tests = b.addTest(.{ .root_module = cli_test_mod });
    test_step.dependOn(&b.addRunArtifact(cli_tests).step);

    // Fuzz smoke test — runs each seed once under the normal test runner.
    const fuzz_mod = b.createModule(.{
        .root_source_file = b.path("src/fuzz_check.zig"),
        .target = target,
        .optimize = optimize,
    });
    fuzz_mod.addImport("type_engine", engine_mod);
    fuzz_mod.link_libc = true; // file_cache.zig → project_cache.zig → std.c.realpath
    const fuzz_tests = b.addTest(.{ .root_module = fuzz_mod });
    test_step.dependOn(&b.addRunArtifact(fuzz_tests).step);

    // `zig build fuzz` — stdin-reading binary for AFL++ / honggfuzz.
    // No server, no IPC, no special runtime required.
    //
    // Quick start:
    //   zig build fuzz
    //   mkdir -p corpus && cp test/fixtures/*.zig corpus/
    //   afl-fuzz -i corpus/ -o findings/ -- ./zig-out/bin/fuzz-zbc
    //
    // Also exports LLVMFuzzerTestOneInput for manual libfuzzer use:
    //   zig cc -fsanitize=fuzzer src/fuzz_check.zig [imports...] -o fuzz-lf
    //   ./fuzz-lf corpus/
    const fuzz_step = b.step("fuzz", "Build AFL++/honggfuzz stdin fuzz target");
    const fuzz_exe_mod = b.createModule(.{
        .root_source_file = b.path("src/fuzz_check.zig"),
        .target = target,
        .optimize = .Debug,
    });
    fuzz_exe_mod.addImport("type_engine", engine_mod);
    fuzz_exe_mod.link_libc = true; // file_cache.zig → project_cache.zig → std.c.realpath
    const fuzz_exe = b.addExecutable(.{ .name = "fuzz-zbc", .root_module = fuzz_exe_mod });
    b.installArtifact(fuzz_exe);
    fuzz_step.dependOn(&b.addInstallArtifact(fuzz_exe, .{}).step);
}
