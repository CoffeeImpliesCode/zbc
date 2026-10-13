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
//!     var root_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
//!     const root_len = try std.Io.Dir.cwd().realPathFile(io, ".", &root_buffer);
//!     const roots = [_][]const u8{root_buffer[0..root_len]};
//!     var session: zbc.Session = undefined;
//!     try session.init(gpa, io, .{ .roots = &roots });
//!     defer session.deinit();
//!     const analysis = try zbc.analyzeEscape(&session, path, &zbc.DefaultConfig);
//!     defer zbc.freeAnalysis(gpa, analysis);
//!
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
    engine_mod.link_libc = true; // engine filesystem tests use realpath

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

    // `zig build check` compiles the CLI without installing it or running the
    // self-check. ZLS build-on-save runs a top-level "check" step when one
    // exists and otherwise falls back to the default step, which reruns the
    // full self-audit of src/ on every save.
    const check_step = b.step("check", "Compile zbc without installing or self-checking");
    check_step.dependOn(&exe.step);

    // ── CLI contract tests: runs the emitted exe against fixtures ─────
    const cli_contract_mod = b.createModule(.{
        .root_source_file = b.path("src/cli_contract_tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    cli_contract_mod.addImport("type_engine", engine_mod);
    cli_contract_mod.link_libc = true; // project_cache.zig uses std.c.realpath

    // The options module points at the executable artifact itself. The
    // path dependency makes the contract-test run build that artifact
    // without requiring the install step or a fixed zig-out location.
    const cli_contract_options = b.addOptions();
    cli_contract_options.addOptionPath("zbc_exe", exe.getEmittedBin());
    cli_contract_mod.addOptions("cli_contract_options", cli_contract_options);

    const test_step = b.step("test", "Run zbc tests");
    const cli_contract_tests = b.addTest(.{ .root_module = cli_contract_mod });
    test_step.dependOn(&b.addRunArtifact(cli_contract_tests).step);

    // Root the artifact at engine.zig so its own test blocks are discovered.
    const engine_tests = b.addTest(.{ .root_module = engine_mod });
    test_step.dependOn(&b.addRunArtifact(engine_tests).step);

    // ── Dogfood: self-check on every `zig build` ────────────
    // The self-check analyses all of src/, and a Debug zbc is roughly eight
    // times slower than ReleaseSafe on that tree, so a Debug build checks
    // itself with a ReleaseSafe copy.  Safety checks stay on.
    const self_check_exe = if (optimize == .Debug) blk: {
        const fast_engine = b.createModule(.{
            .root_source_file = b.path("src/type_engine/engine.zig"),
            .target = target,
            .optimize = .ReleaseSafe,
        });
        fast_engine.link_libc = true;
        const fast_mod = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = .ReleaseSafe,
        });
        fast_mod.addImport("type_engine", fast_engine);
        fast_mod.link_libc = true;
        break :blk b.addExecutable(.{ .name = "zbc-self-check", .root_module = fast_mod });
    } else exe;
    const self_check = b.addRunArtifact(self_check_exe);
    // Budget-partial files are expected on this tree and listed on stderr;
    // findings and failed files still fail the build.
    self_check.addArg("--allow-partial");
    self_check.addDirectoryArg(b.path("src/"));
    // build.zig is an input so its named modules (`@import("type_engine")`)
    // resolve; without it every call into the engine is opaque.
    self_check.addFileArg(b.path("build.zig"));
    b.default_step.dependOn(&self_check.step);

    const run_cmd = b.addRunArtifact(exe);
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run zbc CLI");
    run_step.dependOn(&run_cmd.step);

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
