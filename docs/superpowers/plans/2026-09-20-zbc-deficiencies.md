# ZBC Reliability and Precision Implementation Plan

> **For agentic workers:** Use the available `subagent-driven-development` or `executing-plans` skill to implement this plan task-by-task. Checkbox items below are planned work, not completed fixes.

**Goal:** Make ZBC report analysis coverage honestly, respect first-party scan boundaries, resolve the correct declarations, and remove the reproduced diagnostic errors without hiding real bugs.

**Architecture:** A caller-owned analysis session holds an immutable source snapshot, canonical file identities, and import-scoped model caches. The parser reports incomplete analysis explicitly. Flow rules consume AST operations and path facts; pattern rules report proven violations separately from speculative advice.

**Tech Stack:** Zig CLI/library, embedded ZLS-derived type engine, CFG/worklist analysis, token/AST pattern rules, JSON/SARIF reporting.

## Global Constraints

- Preserve the 38 pre-existing modified files. This assessment did not implement fixes or alter their source.
- Do not scan dependencies of `~/projects/{skript,simd,ocean,zmath,nogui}`. Prune before opening directories; output filtering is not pruning.
- Do not execute analyzed projects' build scripts or fetch their dependencies during analysis.
- Do not silence real bugs to reduce diagnostic counts. Every precision fix needs a safe case and an unsafe control.
- Migrate all callers when changing exported APIs; use LSP references before the cutover. Remove the old global-cache and bare-name paths rather than adding compatibility shims.
- Keep project files unchanged. Tests below concern ZBC, not modifications to the five target projects.
- Maintain one consistent parser/AST representation. Do not bolt a second parser onto rules without a deliberate version-support decision.

## Current state and upstream

- Local HEAD and freshly fetched `origin/main`: `419d153ca411d1698899992d86c51eb9a7e14919` (`lock-held-across-early-exit`, upstream #21).
- Remote: <https://github.com/ericsssan/zbc>. `git ls-remote --heads --tags origin` exposed only `main` as a branch, plus v0.1.0–v0.1.3 tags. No newer upstream revision was available; no merge or local-history rewrite was needed.
- Checkout is shallow and has no `.jj`. Initial changes: 38 files, +5,390/-579 lines. Largest local work is in value-range analysis, CFG/worklist handling, caches, models, and the type-engine adaptation.
- Manifest version: 0.1.3. Compiler pin: `0.17.0-dev.1509+bb296ab9b`; anyzig fetch returns HTTP 404.
- Validation override: `0.17.0-dev.2234+80fe9b2b7`, the master build listed in <https://ziglang.org/download/index.json> during this assessment. The pin was not changed.
- `src/`: 148 Zig files, 92,547 lines including tests. Flow: 16,117 lines; type engine: 23,069; rules: 39,905. Runtime catalog lists **100 rules**. README says 45 and ARCHITECTURE says 46; both need correction.
- Pipeline: CLI expansion → worker-local type context → per-file parser/FileCache → CFG/worklist → pattern catalog → suppressions → sorted diagnostics. A process-global ProjectCache currently supplies cross-file models.

## Verification completed

Compiler executable used for reproducible local commands:

```sh
ZIG=/home/janis/.cache/zig/p/N-V-__8AAH-JQBa12qHq5ZlGFlbzOI3_pZrBVIGZXxTyBNtY/zig
export PATH="${ZIG%/zig}:$PATH"
"$ZIG" build --summary all -j2
"$ZIG" build test --summary all -j2
```

- Standard build: **6/6 steps succeeded**, including self-check and fuzz executable installation.
- Tests: **3,791/3,791 executions passed** across library (1,266), CLI (1,275), and fuzz (1,250) test binaries. This is not a count of unique test definitions.
- Initial test attempt timed out at 180 seconds while preparing the build; the later 900-second-bounded attempt completed in 224.65 seconds. Its reported test runners took about five seconds each.
- A fresh Debug CLI was also built directly from current source for the sweeps; no stale prebuilt executable was used.
- Test helpers also omit parser-error checks (`src/testing.zig:45-50,64-69`). A passing negative rule test is therefore not proof that its whole fixture parsed. Task 1 must close this gap before relying on the green suite as a precision gate.
- `zig build run -- --help` fails: the child receives no arguments, prints usage, and exits 2. `build.zig:64-67` does not forward `b.args`.

### Five-project matrix

Original source bytes were copied into `/tmp/zbc-assessment-6j53ve64/<project>`. Only selected first-party directories and root Zig/build-manifest files were copied; dependency/build/cache directories were pruned before traversal, and symlinks were not followed. The CLI ran against these isolated roots. Its implicit project index could therefore not descend into the original dependency trees.

| Project | CLI-selected Zig files | Exit | Diagnostics | Files with parser errors | Wall time |
|---|---:|---:|---:|---:|---:|
| skript | 75 | 0 | 0 | 11 | 69.227 s |
| simd | 27 | 1 | 20 | 2 | 8.585 s |
| ocean | 128 | 1 | 41 | 31 | 88.253 s |
| zmath | 186 | 1 | 21 | 1 | 5.358 s |
| nogui | 80 | 0 | 0 | 9 | 63.132 s |
| **Total** | **496** | | **82** | **54** | |

A hidden root `.tmp-core-probe.zig` was copied from skript but filtered out by the CLI; it is not included in the 496 selected files. The initial raw copy count was 497. Timing is observed Debug-run latency under concurrent workstation load, not a controlled performance benchmark.

Allowed directories: skript `src,test,bench,lib,web`; simd `src,test,scripts`; ocean `src,test,tools`; zmath `src`; nogui `src,tools,testdata`. Exact selected-file hashes and diagnostics are in `2026-09-20-zbc-evidence.json` beside this plan.

**Coverage limit:** These were analyzer sweeps, not builds/tests of the target projects. Dependencies were absent, so dependency-derived type information was unavailable. A separate probe using the same `std.zig.Ast.parse` found parser errors in 54 selected files. The CLI never disclosed them. Consequently, no zero-report row means “project verified clean,” and no diagnostic count is a confirmed project-bug count.

`zig ast-check` additionally failed on five files for non-parser reasons, making 59 ast-check failures. Do not confuse that count with the 54 AST-parser failures. For example, `[_]u8{0} ** 4` passes Zig 0.16 ast-check, fails the current dev compiler, and still produces exit 0 / `[]` from ZBC. All five target manifests declare Zig **0.16.0**. A separate 0.16 parser probe reduces parser-error files from 54 to **3** (skript Runtime and intrinsics/equal, simd formats/xml); 51 dev-parser failures disappear. This is not a 0.16 analyzer sweep, only a parser comparison. The README's instruction to put the target project's Zig on PATH changes type-engine discovery, **not the parser compiled into ZBC**.

## Confirmed deficiencies and priority

| Priority | Deficiency | Evidence | Impact |
|---|---|---|---|
| P0 | Parse errors and unsupported syntax silently treated as clean | `src/lib.zig:53-54`; invalid/legacy syntax probes return exit 0 and `[]` | False assurance; incomplete matrix coverage |
| P0 | Exclusion checks happen after traversal; implicit global index | `src/main.zig:291-316`; `src/cache/project_cache.zig:561-606`; `src/cache/file_cache.zig:159-166,237-258` | Dependency scans can block; unrelated declarations affect results |
| P0 | Analyzer arithmetic can abort the process | Runtime SIGABRT at `value_range.zig:2359` | One source file terminates the sweep |
| P1 | Unsound range proofs hide invalid subscripts | Mutating `&i` and wrapping-return probes exit 0; unguarded controls report | False negatives, not just noisy warnings |
| P1 | Loop-exit defer is omitted | Loop break probe is clean; direct arena-kill control reports | Real lifetime event missing from CFG |
| P1 | Cache lacks project/declaration identity and explicit lifetime | `src/lib.zig:184-203`; `project_cache.zig:54-78,203-223`; runtime A→B probe resolves B's Marker to A | Cross-project contamination; startup data race; stale imported models |
| P1 | Integer bitwise AND is interpreted as address escape | Minimal integer-only returned-struct probe emits stack-escape | Proven false positives in numeric code |
| P1 | Guarded deferred cleanup loses boolean state | `defer if (owned) free(p); free(p); owned=false;` emits double-free | Correct cleanup paths reported as memory bugs |
| P1 | Qualified types and some interned type variants lose identity | `file_cache.zig:331-346,1279-1304`; `engine.zig:218-236,291-315,361-372` | Wrong cleanup/effect summaries and unresolved type queries |
| P1 | Pattern rules overstate name/shape heuristics as errors | Safe nullable output-pointer probe and project triage below | Low diagnostic precision; unsafe suggested rewrites |
| P2 | JSON/SARIF channel and failure contract | JSON emitted to stderr; missing file yields text plus `[]`, exit 1 | Machine-readable output breaks on operational errors |
| P2 | Build run arguments and architecture docs are stale | Runtime `build run -- --help`; README/ARCHITECTURE counts and paths | Broken development workflow and misleading integration guidance |

### Reproduction controls

All cases were run with the fresh Debug CLI. A real local-pointer escape and a real double-free were correctly reported. A guarded index (`if (n < 2) return 0; bytes[n-1]`) was correctly quiet. These controls must remain correct after fixes.

The cache-identity probe constructs one current ProjectCache and looks up `Marker` from two independent temporary roots. Both roots contain their own Marker declaration. Output:

```text
requested=.../cache-probe/a/main.zig resolved=.../cache-probe/a/main.zig
requested=.../cache-probe/b/main.zig resolved=.../cache-probe/a/main.zig
```

The global initialization race is source-proven, not claimed to have caused a crash in these runs. `global_project` is read/written without synchronization after workers start. Cache mutation itself uses a spinlock, but initialization does not.

## Implementation order

Tasks 1–3 establish trustworthy coverage and lookup. Task 4 restores soundness before new suppression proofs. Tasks 5–10 improve control flow, type resolution and precision. Task 11 closes CLI/documentation gaps. Do not first blanket-disable rules or add target-project suppressions.

### Task 1: Report incomplete analysis and define supported Zig syntax

**Files:** `src/lib.zig:32-115`, `src/main.zig:230-276`, `src/flow/worklist.zig:102-118`, `src/cache/project_cache.zig:517-555`, `src/testing.zig`, `src/fuzz_check.zig`, `build.zig.zon`, `README.md`.

**Contract:** A parse-invalid file is never a clean analysis. Operational failures use exit 2; findings use exit 1; complete analysis without findings uses exit 0. The CLI reports analyzed/failed counts and the parser compiler version. Imported invalid files propagate incomplete resolution rather than cached valid models.

- [ ] Add a failing CLI regression with this complete source:

```zig
pub fn broken( {
```

Require an explicit parse failure and exit 2, not `[]` with exit 0. Add a valid file to the same invocation and require partial completion to remain nonzero.
- [ ] Add a version-compatibility regression using `pub const values = [_]u8{0} ** 4;`. It must either be fully supported by the declared parser version or explicitly rejected as incomplete. Do not silently rewrite source tokens to approximate another language version.
- [ ] Check `tree.errors` before CFG/model/rule dispatch in every parser entry point; keep source locations in the error result. Migrate test helpers/fuzz expectations so invalid input is an expected failure outcome rather than a false clean result.
- [ ] Pin an available compiler with a retained artifact/checksum in CI and document the compiler override. Recommended compatibility target for these five projects: a single parser/type-engine stack aligned with stable Zig 0.16. Port compiler-facing AST/reflection calls and the manifest together, then run the existing analyzer suite before repeating the matrix. Keep the dev build's unsupported-source outcome explicit until that port passes; do not silently translate old syntax or assume changing PATH changes the parser. The parser comparison provides a gate: the same source bytes have 3 parse-error files under 0.16, versus 54 under current dev. Those 3 project-source failures must remain explicit, not be hidden.
- [ ] Replace the worklist's success-shaped return after 200,000 visits with an explicit incomplete-analysis result. Preserve the bound; test budget exhaustion with a generated CFG and require a non-clean outcome. The conservative 50,000-node value-range proof budget is different: exhaustion must withhold a suppression, not fabricate a proof.
- [ ] Run the suite and the exact 496-file manifest. Gate on coverage counts, not only exit status or diagnostic count.

### Task 2: Enforce scan boundaries before traversal

**Files:** `src/main.zig:167-177,291-316`, `src/cache/project_cache.zig:195-255,561-615`, `src/cache/file_cache.zig:151-258`, `src/config.zig`.

**Contract:** One scan policy controls CLI expansion and semantic source loading. Excluded roots are never opened, even through an import. Symlink handling is explicit and cannot escape the allowed canonical roots. Unknown external types stay unknown.

- [ ] Add a temporary project containing `src/main.zig`, a sibling import, and excluded `deps`, `third_party`, `vendor`, `zig-pkg`, `.zig-cache`, and `zig-out` directories. Put a detectable double-free in each excluded tree. Trace filesystem opens and require that the trees are not entered, rather than merely checking that their diagnostics are hidden.
- [ ] Replace `Dir.walk` plus post-filtering with a bounded explicit directory stack that checks names/policy before opening children. Preserve ordinary first-party recursion and deterministic ordering; deduplicate canonical input files.
- [ ] Remove the global name-index fallback from ordinary semantic lookup. Follow only allowed, resolved import edges. Explicitly rejected or unresolved dependencies must not trigger a project-wide name search.
- [ ] Expose `--exclude=<path>` and canonical allowed roots through a shared policy. Include the names above plus node_modules/build/cache outputs as defaults, with documented precedence. Do not claim `.gitignore` support unless implemented and tested.
- [ ] Re-run all five projects directly only after filesystem traces prove exclusion. Until then, keep the isolated-snapshot procedure.

### Task 3: Make cache ownership and declaration identity explicit

**Files:** `src/lib.zig:78-84,178-204`, `src/main.zig:189-228,422-451`, `src/cache/project_cache.zig`, `src/cache/file_cache.zig`, public-library callers in tests/fuzz/build docs.

**Contract:** A session owns immutable source/model state for one analysis sweep. It is initialized before workers and destroyed after they join. Type/method identity includes the canonical source/declaration, never just a leaf name. A new sweep gets a new session; incremental invalidation is not added without an explicit requirement.

- [ ] Keep the A/B Marker regression above and add two imported `Node` declarations with different cleanup methods. Reverse input order; the selected method must not change.
- [ ] Replace `global_project` and `clearProjectCacheForTesting` with explicit session ownership passed through analysis. Unit fixtures use an explicit empty/current-file scope; cross-file tests own their fixture session.
- [ ] Canonicalize absolute and relative input paths once, including `..` and symlink handling under Task 2's policy. Carry declaration identity through `paramContainerName`, imported-type resolution, and method-summary keys; leaf names remain display text only.
- [ ] Remove the global type index. This also removes its prematurely published `type_index_built` latch and unrelated first-match behavior. If any optional index remains, publish it only after complete success and expose load failures rather than caching partial success.
- [ ] Do not hold the coarse spinlock across filesystem I/O or parsing. Prefer worker-owned caches for simplicity, or short locked publication of immutable entries; measure duplication before introducing an in-flight loader abstraction.
- [ ] Define source freshness as snapshot-scoped. A second sweep after editing an imported file must see the edit. A session must not outlive its Io or free borrowed AST/model pointers while workers use them.

### Task 4: Restore sound value-range proofs and checked arithmetic

**Files:** `src/flow/value_range.zig:1858-1894,2284-2378`, `src/flow/value_range_tests.zig`, diff-alias intersection at `value_range.zig:203-207,351-358`.

**Contract:** A proof used to suppress a diagnostic must hold on every feasible incoming path. Unknown mutation, wrapping arithmetic, or a conflicting relation removes the proof. An analyzed integer expression must not cause arithmetic overflow inside the analyzer.

- [ ] Retain this crashing input as a regression; the current Debug CLI aborts with SIGABRT at `ceilDivBase:2359`:

```zig
fn ceil(x: u64) u64 {
    return (x + 18446744073709551615) / 2;
}
pub fn f(x: u64, bytes: []const u8) u8 {
    if (x != 0) {
        const n = ceil(x);
        return bytes[n - 1];
    }
    return 0;
}
```

- [ ] Avoid overflow in the analyzer's comparison. With `dval != 0`, replace `cval + 1 >= dval` by `cval >= dval - 1`. Separately require valid signedness/no-wrap assumptions for the source expression; fixing the analyzer arithmetic alone does not make its nonzero inference sound.
- [ ] Retain the scalar-address-escape regression:

```zig
fn mutate(p: *usize) void { p.* = 0; }
pub fn f(i_in: usize, buf: []const u8) u8 {
    var i = i_in;
    if (i != 0) {
        mutate(&i);
        return buf[i - 1];
    }
    return 0;
}
```

Current CLI result: exit 0 / `[]`; removing the guard makes the warning appear. Remove the incomplete fast-return in `killMutatedContainers`, or include every fact set invalidated by `dropEscapedScalarFacts`. Walk actual address-of arguments, not binary ampersand tokens. By-value reads must retain unrelated facts.
- [ ] Retain the wrapping-summary regression:

```zig
fn wrap(x: u8) u8 { return x +% (0 -% x); }
pub fn f(x: u8, buf: []const u8) u8 {
    if (x != 0) {
        const m = wrap(x);
        return buf[m - 1];
    }
    return 0;
}
```

Current CLI result: exit 0 / `[]`; without the guard it reports the subscript. `wrap` returns zero for every x. Reject wrapping addition as a nonzero postcondition unless ranges prove no wrap. Checked/saturating signed addition also needs a range proof: `x != 0` alone does not imply `x + 1 != 0`.
- [ ] Make diff-alias joins retain only identical/semantically equivalent subtrahend relations. The current comparison ignores `sub_node`. Exercise the resulting public nonzero proof at a merge; if a proposed source case cannot produce that state, keep it as a focused abstract-domain contract test rather than claiming an unobserved program failure.
- [ ] Run the range suite, safe positive-proof controls, and all new CLI reproductions before adding more precision suppressions in the numeric rules.

### Task 5: Distinguish address-of from bitwise AND

**Files:** `src/flow/cfg_builder.zig:4307-4467` (`firstAddressedLocal`, `emitAdditionalEscapeChecks`), `src/flow/cfg_tests.zig`, `src/flow/worklist.zig` only if provenance representation requires it.

- [ ] Retain this complete false-positive regression:

```zig
const Pair = struct { a: u32, b: u32 };
pub fn bits(x: u32) Pair {
    const mask: u32 = 255;
    return .{ .a = x & mask, .b = 0 };
}
```

Expected: no stack escape. Pair it with `pub fn bad() *u32 { var x: u32 = 1; return &x; }`, which must still report one.
- [ ] Use AST `.address_of` nodes for address provenance. Do not infer an address from an ampersand token inside a returned expression/initializer. Binary `.bit_and` cannot create pointer provenance.
- [ ] Apply the same distinction to aggregates, nested expressions, and aliases; do not special-case names such as `mask`.
- [ ] Re-run the zmath remainder and ocean Evaluate cases listed in the triage, plus the full flow suite.

### Task 6: Repair cleanup edges, reachability and branch facts

**Files:** `src/flow/cfg_builder.zig`, `src/flow/cfg.zig`, `src/flow/worklist.zig`, `src/flow/abstract_state.zig`, `src/flow/cfg_transfer.zig`, `src/flow/cfg_tests.zig`.

- [ ] Retain this complete safe cleanup case:

```zig
const std = @import("std");
pub fn safe(gpa: std.mem.Allocator) !void {
    const p = try gpa.alloc(u8, 8);
    var owned = true;
    defer if (owned) gpa.free(p);
    gpa.free(p);
    owned = false;
}
```

Current result: heap-double-free at the deferred free. Expected: no diagnostic. Delete `owned = false` in the unsafe control and require the double-free.
- [ ] Evaluate deferred conditions using exit-time state, including boolean assignments, branch joins and catch/errdefer paths. Avoid merely suppressing diagnostics inside defer.
- [ ] Preserve separate success/error exits so error cleanup does not leak onto successful returns. Unknown branch conditions still require both feasible paths.
- [ ] Replay normal defers on every scope crossed by `break` and `continue`, including labels, in reverse registration order. Do not run errdefer on normal control transfer. The current builder (`cfg_builder.zig:1972-2092`) jumps without flushing them.
- [ ] Retain the confirmed missed-kill case below. Its direct `arena.deinit(); _ = buf;` control reports arena-use-after-kill, while the loop-exit version currently returns exit 0 / `[]`:

```zig
const std = @import("std");
pub fn f(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    const alloc = arena.allocator();
    const buf = try alloc.alloc(u8, 8);
    while (true) {
        defer arena.deinit();
        break;
    }
    _ = buf;
}
```

- [ ] Route natural `while`/`for` exhaustion through the else block when present; only `break` bypasses else. Current direct header-to-merge edges coexist with header-to-else edges (`cfg_builder.zig:1227-1262,1694-1734`). Test observable cleanup effects on natural exhaustion versus early break, not incidental block numbering.
- [ ] Retain reachability from worklist seeding and skip unreachable blocks during diagnostic replay (`worklist.zig:145-163`). An empty abstract state is not a reachability test. Exercise disconnected diagnostic statements with a contract-level synthetic CFG case.
- [ ] Preserve correlations between destroy/insert branches guarded by the same boolean (ocean JIT already_recorded). Do not disable out-parameter checks merely because the function returns bool or writes through a locally named alias.
- [ ] Re-run ocean's guarded ownership cases and all existing errdefer/defer tests.

### Task 7: Normalize type queries and qualified field resolution

**Files:** `src/type_engine/engine.zig:218-375`, `src/model/model_query.zig`, `src/model/file_model.zig`, `src/cache/file_cache.zig`, cleanup/borrow rule callers.

- [ ] Add direct and IP-backed type-value cases (`const Maybe = ?u8; const P = *u8;`) and imported/qualified container cases. Verify optional/pointer/enum/container identity, not internal field copies.
- [ ] Share type normalization across predicates. Respect `is_type_val`: use the denoted `payload.index` for a type value and `payload.type` for a runtime value. Preserve unknown instead of converting unresolved into a proved negative.
- [ ] Resolve the entire field type, including namespace qualification, optional/pointer layers, and nested declarations. Never infer ownership from just the first identifier of `aro.Tree.Node.Index`.
- [ ] Bound wrapper traversal with an explicit unknown result at the limit; do not silently classify a depth-limited unresolved type as safe. Do not claim all IP-backed enums exist in the current engine without a reachable fixture.
- [ ] Re-run both cleanup rules against ocean's AroAdapter integer/ID fields and positive fixtures with actual owned child objects.

### Task 8: Repair numeric-rule proof requirements

**Files:** `src/flow/value_range.zig`, `src/flow/value_range_tests.zig`, `src/rules/misc/index_minus_one_without_zero_guard.zig`, `index_type_narrowing_wraparound.zig`, `midpoint_addition_overflow.zig`, `intfromfloat_without_clamp.zig`, `intcast_of_negated_signed.zig`, `f32_narrowing_int_to_float.zig`.

- [ ] Convert each distinct confirmed numeric false-positive cause in the triage into one minimal safe regression and an unsafe boundary control. Reuse the shared range engine; do not add a separate textual guard recognizer to each rule.
- [ ] Propagate constants, loop induction bounds, relational nonempty facts, and existing range checks. Model helper-return facts only when proved by a summary; never assume a helper is safe from its name.
- [ ] For index narrowing, compare the proved reachable index range with the target width and actual collection capacity. A signed sentinel index into a small fixed table is not automatically a wraparound bug.
- [ ] For float-to-int, require finite/range facts at the conversion. For integer midpoint and signed negation, preserve signedness and overflow semantics. For integer-to-f32, separate intentional rounded conversion from exact-integer requirements.
- [ ] Unknown safety is not proof of a definite error. Record uncertainty and keep genuinely risky unknown cases available as advisory findings rather than asserting a proved violation.

### Task 9: Restrict lifecycle and shape heuristics to evidence

**Files:** `src/rules/misc/double_optional_ptr.zig`, `src/rules/misc/ref_counted_copy_without_dupe.zig`, `src/rules/collection/arraybuffer_slice_without_pin.zig`, `src/rules/errdefer/errdefer_alive_after_ownership_transfer.zig`, `src/rules/cleanup/owned_field_no_outer_cleanup.zig`, `src/problem.zig`, `src/config.zig`, affected rule explainers.

- [ ] Retain this legal API case as a negative regression:

```zig
pub fn report(out: ?*?u32) void {
    if (out) |p| p.* = null;
}
```

It means an optional output slot whose value is optional. Current ZBC calls it an error. Remove the categorical prohibition on `?*?T`; a warning needs an actual inconsistent use or contract, not the type shape alone.
- [ ] Require resolved ownership/effect evidence before treating `run`, `toSlice`, `.data`, `deinit`, or a factory-shaped call as GC/refcount/ownership transfer. Preserve diagnostics for proved resource transfers.
- [ ] Do not recommend resource operations unavailable on the resolved type (for example, Bun `.pin(globalObject)` on ordinary process arguments).
- [ ] For unresolved external types, report incomplete resolution/advisory uncertainty rather than inventing a resource owner. Re-run all 82 diagnostic locations, not just the easiest cases.

### Task 10: Model collection mutation and union observability

**Files:** `src/rules/collection/memset_undef_after_len_truncation.zig`, `src/rules/misc/tagged_union_payload_early_exit.zig` (`assignmentIsObservable`), shared local-binding/provenance helpers only where needed.

- [ ] Add a negative regression for append growth: record old length, reserve `old + count`, assign the new length, then fill `[old..new]` with zero. Require no truncation warning. Pair it with an actual shrink followed by an incorrectly bounded undefined fill.
- [ ] Prove decreasing length and identify the removed range before reporting a truncation violation. A length assignment followed by memset is not sufficient evidence.
- [ ] Add paired union regressions: a caller-visible union with a fallible payload must still report; a new private allocation that is raw-freed on every failing path must not report solely for partial initialization.
- [ ] Improve `assignmentIsObservable` by following the field receiver back to its allocation/capture and cleanup paths. Do not assume RHS evaluation is transactional: both compiler versions tested perform partial retagging. Do not exempt all loop captures or all heap allocations.
- [ ] Re-run ocean Serialize:1398 and RiscvElf:1381 plus the externally visible union positive control.

### Task 11: Repair CLI/build integration and document the contract

**Files:** `src/main.zig` reporters and exit handling, `build.zig:64-67`, `README.md`, `ARCHITECTURE.md`, rule explainers affected above.

- [ ] Send JSON/SARIF data to stdout and operational messages to stderr. Keep stdout parseable on mixed successes/failures; exit 2 signals incomplete analysis. Add CLI subprocess tests for a missing file, malformed source, normal finding and clean input.
- [ ] Forward build-run arguments with the existing Build API:

```zig
if (b.args) |args| run_cmd.addArgs(args);
```

Require `zig build run -- --help` to exit 0 and `zig build run -- --format=json <fixture>` to analyze the supplied file.
- [ ] Update rule counts from the catalog, actual `src/{ast,cache,model,flow}` paths, the current `analyzeEscape`/session signature, parser-version support, exclusions, channels, exit codes and target-type-resolution limitations. Remove stale API examples rather than documenting aliases.
- [ ] Run standard build/self-check, all existing tests, minimal reproductions and the five-project matrix. Review diagnostics against the classified evidence, not a target of zero reports.

## Release gates

- [ ] No dependency directory opens in the five-project filesystem traces.
- [ ] All selected files accounted for as analyzed or explicitly failed; no silent parse-error success.
- [ ] Cache isolation and input-order regressions pass; no global initialization race remains.
- [ ] Safe ampersand/defer/optional-output probes are quiet; genuine escape/double-free controls still fire.
- [ ] All project diagnostics are re-triaged with preserved safe/unsafe controls.
- [ ] JSON/SARIF streams parse, operational failures are distinct, and build-run arguments work.
- [ ] Standard build and existing suite pass on the declared compiler; docs match the shipped contract.

## Diagnostic triage: SIMD and zmath

Source review accounted for all 41 reports: 40 false positives under the observed program contracts, one unresolved numerical-range proof. These are source-review classifications, not a claim that every project path was runtime-tested. Full per-location reasoning is retained in the evidence JSON.

| Project/file | Lines | Classification | Cause |
|---|---|---|---|
| simd `src/core/json_lexical.zig` | 196, 321, 619 | FP (3) | Caller nonempty-block invariant; start/end relation |
| simd `src/core/resident.zig` | 73 | FP (1) | Guard borrows a lease capability; its caller owns release |
| simd `src/formats/xml.zig` | 380, 465, 708 | FP (3) | Loop/block-end and comment-distance bounds |
| simd `src/formats/yaml.zig` | 1085, 1414, 1451, 2328, 2584, 2599, 2618, 2636, 2664, 2682 | FP (10) | Short-circuit, return-path and parser-state nonempty facts |
| simd `src/formats/yaml.zig` | 1130, 1170 | FP (2) | Intentional nullable output pointer to optional failure |
| simd `string_bench.zig` | 20 | FP (1) | Allocation length is body length + 2 |
| zmath `src/ieee_c23_optional_test.zig` | 28 | FP (1) | All observed payload arguments are exactly representable in f32 |
| zmath `src/scalar.zig` | 1595 | FP (1) | 51-entry fixed table |
| zmath `src/scalar_asinhd.zig` | 125 | FP (1) | 35-entry fixed table |
| zmath `src/scalar_cosh.zig` | 383 | FP (1) | 21-entry fixed table |
| zmath `src/scalar_exp10d.zig` | 125 | FP (1) | 49-entry fixed table |
| zmath `src/scalar_exp2.zig` | 230 | FP (1) | 43-entry fixed table |
| zmath `src/scalar_expm1d.zig` | 236 | FP (1) | 38-entry fixed table |
| zmath `src/scalar_sinhd.zig` | 168 | FP (1) | 51-entry fixed table |
| zmath `src/scalar_tanh.zig` | 8701 | FP (1) | Small fixed literal table |
| zmath `src/scalar_tanpid.zig` | 163 | FP (1) | Small fixed literal table |
| zmath `src/scalar_asin.zig` | 426 | FP (1) | Midpoint bounds from a 29-entry table |
| zmath `src/scalar_exp10m1d.zig` | 258 | FP (1) | All comptime table sizes are at most 145 |
| zmath `src/scalar_exp2m1d.zig` | 206 | FP (1) | All comptime table sizes are at most 93 |
| zmath `src/scalar_hypot.zig` | 226 | FP (1) | Caller restricts operands to subnormal significands |
| zmath `src/scalar_integer_rounding.zig` | 30, 50 | FP (2) | Dominating helper proves finite i64 range |
| zmath `src/scalar_log1pd.zig` | 481 | Unresolved (1) | Private helper needs caller-derived approximation bound |
| zmath `src/scalar_tanpif.zig` | 65 | FP (1) | Exponent cutoff bounds conversion input |
| zmath `src/scalar_narrow_common.zig` | 386 | FP (1) | Supported IEEE formats bound shift far above minInt(i32) |
| zmath `src/scalar_remainder.zig` | 83, 90 | FP (2) | Scalar bitwise AND is not address-of |

For `log1pd`, a Debug smoke probe made **71,634 finite-domain calls**: maximum finite positive input, two representable values immediately above -1, small-value edges, neighbors of every normal exponent, and deterministic positive finite samples. No panic or non-finite result occurred. This does **not** prove every input safe or prove the flagged internal branch was reached. Keep the report unresolved until the approximation range is established; do not label it a confirmed project bug.

## Diagnostic triage: ocean

All 41 emitted locations were reviewed. Conservative accounting: **27 source-reviewed false positives**, plus **14 unsupported ownership claims** whose true imported declarations cannot be checked without the excluded aro dependency. None is reported here as a confirmed project bug.

| File | Lines | Classification | Cause |
|---|---|---|---|
| `src/occ/AroAdapter.zig` | 72, 78, 88, 99, 115, 120, 175, 185, 1575, 3671, 3696, 3697, 3745, 3767 | Unsupported (14) | Qualified node/token handles collapsed to namespace `aro`; dependency unavailable |
| `src/occ/main.zig` | 6 | FP (1) | Ordinary process args mistaken for GC-managed buffer |
| `src/ocean/ImageSafetyTests.zig` | 155 | FP (1) | Pointer mutation mistaken for ownership transfer |
| `src/ocean/backend/riscv/Assembler.zig` | 89 | FP (1) | Range starts at 1 after a length check |
| `src/ocean/backend/spirv/FuzzTests.zig` | 291 | FP (1) | Generated count is at least 2 |
| `src/ocean/backend/spirv/Structured.zig` | 916, 1027 | FP (2) | Earlier validation rejects empty instruction blocks |
| `src/ocean/backend/wasm/FuzzTests.zig` | 317, 385 | FP (2) | Count is at least 2; later byte access follows expect(len >= 1) |
| `src/ocean/backend/wasm/Lower.zig` | 1114, 1128 | FP (2) | Dominating canEmitDiamond/canEmitLoop contracts prove nonempty inputs |
| `src/ocean/backend/wasm/TargetAdapter.zig` | 906 | FP (1) | estimates_released disables errdefer after explicit free |
| `src/ocean/backend/x86_64/EmissionTests.zig` | 211, 413 | FP (2) | Positive fixture length; dominating length assertion |
| `src/ocean/code/Image.zig` | 780 | FP (1) | Range starts at 1 under len > 1 |
| `src/ocean/compile/Driver.zig` | 3197 | FP (1) | snapshot_pointers_freed disables defer |
| `src/ocean/compile/Driver.zig` | 3775, 4057 | FP (2) | Borrowed ModuleView pointer copies, not owned/refcounted value copies |
| `src/ocean/ir/Serialize.zig` | 1398 | FP (1) | Partial union state is confined to a local allocation raw-freed on failure |
| `src/ocean/ir/Serialize.zig` | 1909 | FP (1) | Edit handle borrows the Function; errdefer still owns cleanup |
| `src/ocean/jit/Cache.zig` | 597, 632, 634 | FP (3) | already_recorded makes destroy and insertion mutually exclusive |
| `src/ocean/lower/Evaluate.zig` | 433 | FP (1) | Validated source IDs start at 1 |
| `src/ocean/lower/Evaluate.zig` | 1919 | FP (1) | Integer bitwise AND mistaken for stack address |
| `src/ocean/object/RiscvElf.zig` | 851, 1451 | FP (2) | Validated ranges start at 1 |
| `src/ocean/object/RiscvElf.zig` | 1381 | FP (1) | Appended range filled after growth, not truncated range |

### Independent correction: Zig union assignment is not transactional

The initial source review incorrectly assumed a fallible RHS leaves the old tagged union unchanged. An independent executable probe disproved this on **both Zig 0.16.0 and 0.17.0-dev.2234**:

```zig
const Value = union(enum) {
    old: u64,
    payload: struct { first: u64, second: u64 },
};
fn maybe(fail: bool) !u64 {
    if (fail) return error.InputFailure;
    return 9;
}
fn update(value: *Value, fail: bool) !void {
    value.* = .{ .payload = .{ .first = 42, .second = try maybe(fail) } };
}
```

Starting from `.old = 123`, `update(&value, true)` fails with the active tag already changed to `payload`. **Keep the retagging rule.** The ocean site is safe for a different reason: `fields` is allocated locally at Serialize:1385, raw-freed by errdefer at :1389, and not passed to `module.addLayout` until :1417 after the whole initialization loop succeeds. No error-path code inspects the partial payload.

Likewise, a scalar return type alone does not make an out-parameter lifetime warning false: a bool-returning function can still store a dangling pointer in caller storage. The JIT false positives rest on the `already_recorded` path predicate, not on a blanket exemption for scalar returns or local aliases into `self`.

## Flow review: proof status and remaining checks

The full source review covered CFG lowering, worklist, transfer, abstract state and the shared value-range oracle. New runtime evidence materially changes the priority: this is not only a false-positive cleanup.

| Finding | Evidence status | Planned action |
|---|---|---|
| `ceilDivBase` computes `maxInt(u64) + 1` | Reproduced SIGABRT, exact stack frame :2359 | Task 4 |
| Scalar facts survive `mutate(&i)` | Reproduced missed warning; unguarded control fires | Task 4 |
| Wrapping return inferred nonzero | Reproduced missed warning; unguarded control fires | Task 4 |
| Loop-body defer skipped on break | Reproduced missed arena kill; direct-kill control fires | Task 6 |
| Bitwise AND interpreted as address-of | Reproduced false stack escape | Task 5 |
| Guarded deferred free ignores final flag | Reproduced false double-free | Task 6 |
| Worklist visit limit returns success | Source-confirmed; limit was not reached in project sweeps | Task 1 explicit incomplete status |
| Loop else has a bypass edge | Source-confirmed; no standalone runtime counterexample claimed | Task 6 |
| Diagnostic pass replays unreachable blocks | Source-confirmed; no standalone runtime counterexample claimed | Task 6 |
| Diff-alias join ignores subtrahend identity | Source-confirmed comparison defect; reachable AST counterexample not yet established | Task 4 proof-domain test |
| Branch capture restoration is inconsistent | Review candidate, **not a confirmed valid-program defect** | Require a valid scope-resolution regression before a semantic change |

The review proposed an outer `p` shadowed by `if (opt) |p|`. The compiler rejects that source (`capture 'p' shadows local constant from outer scope`). It is therefore not evidence of a missed bug in a valid Zig program. Do not add that invalid fixture as a claimed soundness regression.

Lower-priority precision work: conjunction refinement retains only part of a multi-fact condition, and raw ampersand scanning can over-invalidate value-range facts. These lose useful proofs rather than establish unsafe ones; address them after the confirmed unsoundness fixes. Cache reset/concurrent teardown, absolute path aliases, index poisoning and IP-backed type handling are covered by Tasks 3 and 7; their full application-level failure rates were not measured here.

## Delivery scope

This document is an assessment and implementation plan, not an implemented fix. No analyzer source or target-project source was changed by this assessment. Available upstream was fetched and found already current. Build outputs and the anyzig compiler cache were refreshed during validation. Only this plan and its JSON evidence are new tracked-file candidates.

The JSON contains all 496 selected-file hashes, all 82 diagnostics with per-location classifications, parser-error lists, and raw minimal-probe outcomes. Temporary executable probes and snapshots remain under `/tmp/zbc-assessment-6j53ve64`; the durable evidence does not depend on their continued existence.

## Verification overlay: 2026-10-07

This section records later verification. The original assessment, source-review classifications, compiler observations, and unchecked plan items remain historical evidence.
An unchecked item above does not override a verified result below. These results do not close every task or release gate.

### Verified CLI contract

- The parent ran all 28 CLI subprocess tests successfully.
- A separate 25-case CLI smoke run covered the issue 81–85 cases and unsafe controls.
- A two-worker mixed run selected four files and failed two. It retained findings from successful files and returned exit 2.
- JSON stdout contained a bare diagnostic array. SARIF stdout contained the SARIF document. Coverage and operational errors used stderr.
- Exit 0 means complete analysis without findings. Exit 1 means complete analysis with findings. Exit 2 means incomplete analysis or an operational failure.
- Filesystem traces covered 260 syscall records. Excluded source trees had no read-capable opens, positive reads, directory enumeration, or mapped reads.
  Positive controls confirmed source reads outside those exclusions. This is fixture-level boundary evidence, not a new five-project matrix.

### Verified public Session contract

- The parent compiled and ran an external named-module consumer with caller-owned `Session`, allocator, I/O, and source policy.
- A genuine finding retained its original AST location: line 3, column 5, byte 50.
- A new session saw replacement source and reported no finding for the safe replacement.
- Invalid source returned `error.InvalidSyntax` with `expected_token` at line 1, column 8, byte 7.
- A disallowed root failed before the consumer read the outside source.
- Root strings remain borrowed. Callers must keep the policy inputs, allocator, and I/O backend alive until session teardown.

### Verified compiler pin and rule retirement

- The current compiler pin is Zig 0.16.0. The original development-compiler results above describe the September assessment only.
- The exercised CLI listed 112 supported invariants and 99 documented rules.
- The categorical `double-optional-ptr` rule is retired. Its detector, explainer, and list entry are absent.
  `--explain double-optional-ptr` returned exit 2. An optional pointer to an optional value is not itself a defect.

### Limits of this overlay

These results do not establish a passing full test suite or default build. They do not establish that all 89 assessed issues are fixed.
They do not replace the original five-project matrix, per-location diagnostic review, or release gates.
The final integration record belongs here, after the parent completes the full build, suite, and runtime gates.
That record must identify the final source state, compiler, commands, outcomes, and remaining failures.
