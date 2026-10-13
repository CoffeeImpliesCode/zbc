# zbc

Infers Zig lifetime, ownership, and cleanup bugs from your code — no
annotations, no runtime instrumentation.

## Example

```zig
const Owner = struct {
    data: []u8,
    pub fn deinit(self: *Owner, gpa: Allocator) void { gpa.free(self.data); }
};

var owner = Owner{ .data = try gpa.alloc(u8, 16) };
const x = owner.data;
owner.deinit(gpa);   // frees self.data — zbc reads the body to know this
_ = x;               // → heap-use-after-free
```

## Build integration

This checkout pins Zig **0.16.0**. Use that compiler to build zbc.
Changing the Zig executable on `PATH` does not change the parser compiled into zbc.
The examples below use the current local checkout, not an older release tag.

The default `zig build` also runs zbc on its own `src/` and `build.zig`.
A default Debug build uses a separate ReleaseSafe binary for this self-audit.
An explicit non-Debug optimization mode uses the CLI binary built with that mode.
The self-audit passes `--allow-partial`; a finding or a failed file fails the build.
`zig build check` compiles the CLI without installing it or running the self-audit.
ZLS build-on-save runs a top-level `check` step when one exists, so editor saves do not start the audit.

```sh
zig fetch --save /path/to/zbc
```

```zig
// build.zig
const zbc_dep = b.dependency("zbc", .{
    .target = target,
    .optimize = .ReleaseFast,
});

const zbc_run = b.addRunArtifact(zbc_dep.artifact("zbc"));
zbc_run.addArg("src/");

b.default_step.dependOn(&zbc_run.step);
```

## Library API

Add the published module to your executable's imports:

```zig
exe.root_module.addImport("zbc", zbc_dep.module("zbc"));
```

The caller supplies the allocator, I/O, and canonical allowed roots.
This example returns the number of findings for one source file:

```zig
const std = @import("std");
const zbc = @import("zbc");

pub fn countFindings(
    gpa: std.mem.Allocator,
    io: std.Io,
    root_path: []const u8,
    source_path: []const u8,
) !usize {
    var root_buf: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const root_len = try std.Io.Dir.cwd().realPathFile(io, root_path, &root_buf);
    const roots = [_][]const u8{root_buf[0..root_len]};
    const policy: zbc.SourcePolicy = .{ .roots = &roots };

    var session: zbc.Session = undefined;
    try session.init(gpa, io, policy);
    defer session.deinit();

    const analysis = try zbc.analyzeEscape(&session, source_path, &zbc.DefaultConfig);
    defer zbc.freeAnalysis(gpa, analysis);
    if (analysis.incomplete.len != 0) return error.AnalysisIncomplete;
    return analysis.problems.len;
}
```

Initialize `Session` in place. Do not move, copy, or share an initialized session between workers.
Keep its allocator and I/O backend alive through `session.deinit()`.
`SourcePolicy.roots` and `SourcePolicy.excludes` borrow their slices and strings.
Keep them alive and unchanged until session teardown. Empty roots deny all source access.

Use a new session for a new source snapshot, including edits to imported files.
`analyzeEscape` borrows its path and configuration only for the call.
It returns an `Analysis`. `problems` holds findings from completed units.
`incomplete` lists functions, summaries, or rules that exhausted an analysis budget.
A listed unit contributes no findings. Other units retain their findings.
An empty `incomplete` means no unit exhausted an analysis budget.
Each `Incomplete` holds its `kind` (`function`, `summary`, or `rule`), its `name`, and an optional `zbc.budget.Diagnostic`.
The diagnostic identifies the limit, its value, the value reached, the canonical source document, and the source position.
It is null when the walk recorded no limit.
The result owns its text and can outlive the session.
Release it with `freeAnalysis` and the session's allocator.

Invalid syntax in an input or import returns `error.InvalidSyntax`, not a clean result.
Read `session.parse_failure` before the next analysis call or session teardown.
It contains the original parser location and reason.
See [ARCHITECTURE.md](ARCHITECTURE.md) for import resolution and internal cache lifetimes.

## CLI

For standalone use:

```sh
zig build -Doptimize=ReleaseFast
zbc src/
zbc --format=compact src/   # grep-friendly
zbc --jobs=2 --exclude=vendor --format=json src/
zbc --zig=/opt/zig-0.16.0/zig src/   # pick the toolchain explicitly
zbc --format=sarif src/
zbc --list-rules
zbc --list-invariants
zbc --explain <rule-id>
```

zbc locates the Zig standard library by running `zig env`.
It uses `zig` from `PATH`, or the executable named by `--zig=<path>`, and needs Zig **0.16.0**.
If that command cannot start, exits nonzero, prints nothing, prints an unusable environment, or reports another version,
zbc prints one error that names the command, its exit status and the first line of its stderr, then analyzes nothing.
The run exits 2, the coverage line counts every selected file as failed, and JSON stdout is still `[]`.
Running from a directory that has no `build.zig.zon` can make the `anyzig` shim exit 1 silently; pass `--zig=` with the real compiler.

`--jobs=<n>` requires a positive decimal integer.
The default uses the CPU count, with a fallback of four.
The worker count never exceeds the number of selected files.

Repeat `--exclude=<path-or-name>` to add exclusions.
A bare name matches an exact basename at any depth.
A path matches its subtree, relative to the current directory unless absolute.
Exclusions are not globs. zbc does not use `.gitignore`.
Exclusions override allowed roots and apply to imported source too.

zbc prunes dot-prefixed components and these directory names before traversal:
`deps`, `dependencies`, `third_party`, `third-party`, `vendor`, `vendored`,
`node_modules`, `zig-pkg`, `zig-cache`, `zig-out`, `build`, `target`, `out`, and `dist`.
Canonical-path checks reject symlink targets outside allowed roots or inside excluded subtrees.
An explicitly requested excluded input fails selection. Excluded children do not count as selected files.

JSON and SARIF reports use stdout. JSON is a bare diagnostic array, including `[]` on failure.
Coverage and operational errors use stderr. Successful files retain their findings when another file fails.
SARIF marks an incomplete run with `executionSuccessful: false`.

The coverage line reports `selected`, `analyzed`, `partial`, `failed`, `findings`, the parser version,
and `unresolved-import-lookups`. `selected = analyzed + partial + failed`.
A file is `partial` when a function, summary, or pattern rule records an exhausted analysis budget.
Selection failures count as failed. Pruned children do not count.
zbc keeps findings from completed units in a partial file.
It prints one stderr line for each incomplete unit:
`zbc: incomplete <file>: fn <name>` or `zbc: incomplete <file>: rule <id>`.
The line identifies the limit and its value, the value reached, and the source position when available.
The position suffix is `at <document>:<line>:<column>`, or `at <document>+<byte>` without a line.
The document can be an imported file. An unknown document prints as `<unknown>`, not as the analyzed file.
Without a recorded limit, the line states that the analysis budget was exhausted.
Work-budget exhaustion marks the affected unit incomplete. That unit contributes no findings.
Some internal proof-query depth cutoffs instead leave the proof unproved, without marking the unit incomplete.
Neither outcome establishes a finding or a positive safety proof.
A file without findings can still be partial.
`findings` counts unsuppressed diagnostics, not files.
Unresolved import lookups are a separate count, not proof of complete external type resolution.

Parse failures report the original source location and parser reason.
The parser uses the pinned compiler. A malformed imported file makes its importer's analysis incomplete.

Exit 0 means complete analysis without findings.
Exit 1 means complete analysis with findings.
Exit 2 means incomplete analysis or an operational failure, even when other files produce findings.
Without `--allow-partial`, a partial file always gives exit 2.
With `--allow-partial`, a partial file alone does not give exit 2.
Findings still give exit 1, and a failed file or an operational failure still gives exit 2.
The coverage line and the `zbc: incomplete` lines are unchanged, and SARIF still marks the run unsuccessful.

## Rules

The analyzer checks 112 supported invariants and documents 99 rules (2026-10-13 CLI lists).
It uses two analysis families:

**Flow analysis** uses a per-function CFG and abstract interpretation.
It checks these invariants:
`allocator-mismatch`, `arena-escape`, `arena-use-after-kill`,
`heap-double-free`, `heap-leak`, `heap-use-after-free`,
`interior-pointer-destroy`, `partial-union-write`, `stack-escape`,
`use-undefined`.

**Pattern detectors** use per-function or per-file token and AST walks.
They check recurring bug shapes in heap lifetime, cleanup, pointer stability,
tagged unions, lifecycle handling, concurrency, and numeric bounds.

The lists have different purposes. `zbc --list-invariants` lists every supported
invariant. `zbc --list-rules` lists the documented catalog.
`zbc --explain <rule-id>` shows one documented rule's rationale, bug, and fix.
The catalog and dispatch table are in `src/rule_catalog.zig`.
The invariant list is in `src/config.zig`.

The categorical `double-optional-ptr` rule is retired.
An optional pointer to an optional value is valid Zig and is not itself a bug.

### Reporting contract

zbc reports proved problems, except for the advisory numeric warnings below.
An unresolved result does not prove a lifetime or initialization bug.
Silence is not a proof that the code is safe.

`stack-escape` reports only proved escapes of function-local storage.
Unresolved field chains and opaque call results stay silent.
Known direct loans still report, including local addresses carried by returned aggregates.
`borrowed-slice-into-stack-buffer-returned` uses the same proved-loan contract.
Possible argument retention or mutation in an incomplete storage query is not a finding.

`use-undefined` reports only reads of proved-undefined bytes.
Return, copy, assignment, by-value arguments, and whole-value `@memcpy` silently transport partially undefined values.
Zig allows copying undefined bytes. Transport of an entirely proved-undefined value reports.
Transport preserves holes, including into the caller. A later selected read of a proved-undefined part reports at that read.
Selected reads include indexing, field access, arithmetic, comparisons, branches, and passing a selected element by value.
Unknown content stays silent. Copies from container-level constants carry unknown holes, not undefined holes.
A direct selected read on the constant still reports proved-undefined bytes.
Strict initialization certificates are unchanged.
An explicit `return undefined;` remains an intentional exception.
Opaque results stay unknown. A missing initialization certificate alone is not a finding.

These numeric rules warn when a required safety property is not proved:

- `index-type-narrowing-wraparound`: the input must fit the destination integer.
- `intfromfloat-without-clamp`: the input must be finite and within the destination conversion range.
- `f32-narrowing-int-to-float`: the integer input must be exactly representable at the destination precision.

These warnings are advisory. They do not claim that every reachable input fails or loses precision.

## False positives and missed bugs

If zbc fires on correct code (false positive) or misses a real bug (false
negative), please [open an issue](https://github.com/ericsssan/zbc/issues)
with a minimal reproducer.  Both matter — FP reports drive suppression
improvements, FN reports drive new rules and deeper inference.

## Suppressions

Silence a false positive with a source comment:

```zig
buf[idx - 1] // zbc-disable-line: index-minus-one-without-zero-guard

// zbc-disable-next-line: heap-use-after-free
_ = ptr;

_ = val; // zbc-disable-line: *   (all rules on this line)
```

## Sponsor

If zbc saves you debugging time, consider [sponsoring development](https://github.com/sponsors/ericsssan).

## Acknowledgements

- [ZLS](https://github.com/zigtools/zls) — type-resolution internals
  (`DocumentStore`, `InternPool`, `Analyser`) extracted and adapted into
  `src/type_engine/` as zbc's embedded type engine.  Not imported as a
  package; vendored and modified in-tree.
