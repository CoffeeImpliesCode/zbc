# zbc architecture

zbc is a static analyzer for Zig, pinned to Zig 0.16.0.
It checks 112 supported invariants and documents 99 rules (`--list-invariants`, `--list-rules`, 2026-10-13).
It uses two analysis families:

1. **Flow analysis** uses a per-function control-flow graph and abstract interpretation.
   It tracks values across branches, loops, defers, captures, and output parameters.
   It reports proved lifetime, ownership, and initialization problems.
2. **Pattern detectors** use per-function or per-file token and AST walks.
   They check recurring bug shapes without the full flow pipeline.

Both families produce `Problem` values for the same reporter.

## Reporting contract

Rules report proved problems, except for advisory numeric warnings.
`stack-escape` requires a proved loan from function-local storage.
Unresolved field chains and opaque call results stay silent. Direct proved loans still report.
`borrowed-slice-into-stack-buffer-returned` also requires a proved expression loan.
Conservative call-argument and event dependencies remain available to storage queries,
but cannot serve as escape witnesses.
Silence is not a safety certificate.

`use-undefined` reports reads of proved-undefined bytes, not missing initialization certificates.
Whole-value return, copy, assignment, by-value arguments, and `@memcpy` silently transport partially undefined values.
Zig allows copying undefined bytes. Transport preserves holes in the destination, including into the caller.
A later selected read of a proved-undefined part reports at that read.
Selected reads include indexing, field access, arithmetic, comparisons, branches, and passing a selected element by value.
Transporting an entirely proved-undefined value reports, except for the intentional literal `return undefined;`.
Unknown values alone remain silent and supply no positive initialization certificate.
Copies from container-level constants carry unknown holes, not undefined holes.
A direct selected read on the constant still reports proved-undefined bytes.
Strict initialization certificates are unchanged.
Prefix joins first record common numeric predicates while each input still has its original bounds.
They retain path-local predicates until empty-prefix entailment is checked, then remove predicates not proved by both inputs.
Capacity-clipped push prefixes require a capacity guard at a selected read; copying a count does not remove that requirement.

`index-type-narrowing-wraparound`, `intfromfloat-without-clamp`, and `f32-narrowing-int-to-float` retain advisory warnings.
They warn when the required integer range, finite conversion range, or exact float representation is not proved.
These warnings do not prove that every reachable input fails.

The authoritative lists have different purposes:

- `src/config.zig::all_invariants` lists the supported invariants.
  `--list-invariants` prints their CLI names.
- `src/rule_catalog.zig::all` contains the documented rules.
  `--list-rules` prints this catalog. `--explain <rule-id>` prints one entry.
- `src/rule_catalog.zig::escape_detectors` dispatches pattern detectors.
  The CFG and worklist pipeline emits flow diagnostics separately.

Catalog size is not the detector count. Do not derive the pattern count
by subtracting flow rules from the invariant list.
The categorical `double-optional-ptr` detector and its catalog entry are retired.

This document describes the shared AST, cache, and model infrastructure.
The flow-analysis modules are in `src/flow/`.

## File layout

```
src/
├── lib.zig                   — public Session and analysis API
├── main.zig                  — CLI
├── problem.zig               — Problem / Note / Pos / Severity
├── config.zig                — Config and supported invariants
├── rule_catalog.zig          — documented catalog and pattern dispatch
├── ast/
│   ├── tokens.zig            — token primitives
│   ├── scope_iter.zig        — scope-aware iterators
│   └── token_query.zig       — token-level pattern queries
├── model/
│   ├── method_names.zig      — name classifiers
│   ├── file_model.zig        — per-file types and functions
│   ├── model_query.zig       — AST-level model queries
│   ├── local_bindings.zig    — per-function binding origins
│   └── fn_summary.zig        — function effects and origins
├── cache/
│   ├── file_cache.zig        — per-analysis shared state
│   └── project_cache.zig     — session-scoped imported models
├── type_engine/
│   ├── document_store.zig    — original source and AST documents
│   └── source_policy.zig     — source admission and canonical identity
├── flow/
│   ├── cfg.zig               — control-flow representation
│   ├── cfg_builder.zig       — AST lowering
│   ├── worklist.zig          — flow-analysis driver
│   ├── abstract_state.zig    — abstract domain
│   └── cfg_transfer.zig      — transfer functions
├── testing.zig               — rule-test helpers
├── trace.zig                 — optional decision logs
└── rules/
    └── <family>/
        ├── <rule_name>.zig   — detector implementation
        └── <rule-name>.md    — rule documentation
```

Rules import internal modules directly. A rule in `src/rules/<family>/` uses:

```zig
const lexer = @import("../../ast/tokens.zig");
const scope = @import("../../ast/scope_iter.zig");
const fmodel = @import("../../model/file_model.zig");
const local = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const mq = @import("../../model/model_query.zig");
const testing = @import("../../testing.zig");
const trace = @import("../../trace.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
```

External library consumers use the published `zbc` module, not these internal paths.

## Session, source identity, and imports

`src/lib.zig` publishes `Session`, `SourcePolicy`, `analyzeEscape`, `Analysis`, and `freeAnalysis`.
`build.zig` registers the `zbc` module and supplies its `type_engine` import.
Consumers add `zbc_dep.module("zbc")` to their module graph and use `@import("zbc")`.
The README gives the caller-owned initialization and cleanup sequence.

Initialize a `Session` in place with an allocator, `std.Io`, and `SourcePolicy`.
Do not move or copy it after initialization. Each CLI worker owns a separate session.
The allocator and I/O backend must outlive the session.
`initWithToolchain` also borrows its caller-owned `Toolchain` until session teardown.
Policy roots, exclusions, and their strings remain borrowed and unchanged during that lifetime.
Roots must be canonical absolute paths. Empty roots deny all source access.
Exclusions override roots, including roots nested within an excluded subtree.

The session owns a `TypeContext` and `ProjectCache` for one source snapshot.
Its document store retains original source bytes and their `std.zig.Ast` trees.
Project models borrow those trees. Flow and pattern analysis use the same original tree.
The parser does not rewrite source to approximate another Zig version.
Diagnostics therefore retain original token locations and byte offsets.

Source identity comes from OS-backed canonical paths.
Relative spellings, `..`, and symlinks resolve through the filesystem, not lexical path folding.
The policy checks source admission before reads and checks canonical targets again.
An excluded import cannot authorize a wider scan.

Relative imports resolve from the importing document's directory.
Named imports resolve from statically parsed `build.zig` module declarations and import chains.
The analyzer reads build scripts. It does not execute them.
Discovered environments must agree on a named module's declared root.
Conflicting or missing mappings stay unresolved, and source policy still gates a resolved root.
Lookup follows import edges, not a process-global search for matching type names.
Type and method identity includes the canonical source declaration, not only a leaf name.

Contextual actual generic bindings can follow references to ancestor declarations.
They do not change the lexical container that `@This()` names.
If the actual and lexical containers have the same canonical owner, resolution retains the actual instantiation.
Otherwise, resolution instantiates the lexical container with the applicable actual generic bindings.
A nested container therefore cannot replace an ancestor's self-type alias with its own type.

Completed type-value memoization retains positive results only.
A null entry reserves an active recursive query, not a completed unknown result.
Unresolved results and errors remove that reservation as the query unwinds.
An enclosing explicit type can then establish a positive result for later queries.

Strict source admission still applies, and errors still propagate.
The memo does not retain unresolved results or errors.
This contract needs no generations, cache resets, or detector-specific retries.

Generic substitution is a pure function of its operands, so each resolver settles it once.
`resolveGenericType` answers a question that binds none of the parameters its type names as that type, without allocating.
Every other question is remembered under the whole type and every binding, and a distinct binding or pointer constness is a distinct question.
A call site's instantiation of a callee's container and declared return value is remembered the same way.
The state-dependent re-read of a value-dependent return type is not remembered; it runs on every call.
These memos and the resolved-node memo live as long as their resolver: one per analysed file, plus one per borrowed source document until the file's analysis ends.

Use a new session after source changes. The current session does not provide incremental invalidation.
`analyzeEscape` borrows its path and configuration only during the call.
It returns an `Analysis` with `problems` and `incomplete`.
Both own their text and strings, so they can outlive the session.
Release them with `freeAnalysis` and the session's allocator.
Internal AST, model, and summary pointers do not have that detached-result lifetime.

Invalid syntax in an input or import returns `error.InvalidSyntax`.
`session.parse_failure` holds the original parser reason and location until the next analysis or teardown.
Imported failures identify the imported document. The input file uses the caller's input path.
An empty diagnostic result is not a successful parse-error outcome.

## CLI selection and reporting

The CLI applies source policy during input expansion and semantic source loading.
It prunes excluded children before directory traversal.
An explicitly requested excluded path fails selection. A pruned child is not selected.
The README lists default exclusions and the exact `--jobs=<n>` and `--exclude=<path-or-name>` forms.

JSON stdout contains a bare diagnostic array. SARIF stdout contains a SARIF 2.1.0 document.
Coverage and operational errors use stderr, not the report stream.
Successful files retain their findings when another selected file fails.
SARIF marks an incomplete run, including one with a partial file, with `invocations[0].executionSuccessful: false`.

Coverage reports `selected = analyzed + partial + failed` and counts unsuppressed findings separately.
Failed selection operands count as selected failures. Parse and analysis failures do not count as analyzed.
A file with a non-empty `Analysis.incomplete` counts as `partial`, never as analyzed or failed.
The CLI prints its findings in every format and one `zbc: incomplete` stderr line for each part that gave up.
Budget positions name their own canonical source document, including imported files.
The suffix is `at <document>:<line>:<column>`, or `at <document>+<byte>` without a line.
In-flight and memo records use `budget.Diagnostic`, which borrows session-owned paths and has no destructor.
`appendIncomplete` and `runOne` copy paths into `budget.OwnedDiagnostic` before their results can outlive the session.
Only the owning type releases the copied path; empty paths need no allocation.
Memoized failures retain the first diagnostic's document and position.
Unresolved import lookups have a separate counter.
That counter is not proof that external types resolved completely.

Exit 0 means complete analysis without findings. Exit 1 means complete analysis with findings.
Exit 2 means an operational failure or incomplete analysis and takes precedence over findings.
Malformed imported source reports its own location and makes the selected importer's analysis incomplete.

## Per-file shared state + dispatch

`analyzeEscape(&session, path, config)` creates one `FileCache` for the call.
It destroys that cache before returning. The flow pipeline and pattern dispatch share it.
The session retains source documents and imported models across calls within the same snapshot.
No process-static project cache participates in this path.

### Analysis budgets

Call-effect and returned-storage queries use fixed per-query limits: 50,000 work units and nesting depth 64.
Normal and error cleanup queries use the same work and depth limits.
Nested queries spend the enclosing query's counter. They do not receive a fresh allowance.
The depth limit measures active nesting, not the number of functions or statements.
The numeric oracle also limits each query to 50,000 steps.
Other bounded walks and fixpoint phases record budget failures through `src/budget.zig`.

Work-budget exhaustion raises `error.AnalysisBudgetExceeded`.
Some internal proof-query depth cutoffs instead leave the proof unproved.
These cutoffs block completed-proof memoization and do not make the unit incomplete.
Neither work-budget exhaustion nor a depth cutoff produces a finding or a positive safety proof.
Depth limits in other walks can raise `error.AnalysisBudgetExceeded` and make the unit incomplete.

The call runs three stages: the file-level summary pass, the per-function flow check, and the pattern rules.
A stage unit is one function (or one function's summary) or one pattern rule.
When a unit raises `error.AnalysisBudgetExceeded`, the analyzer discards that unit's findings and continues with the next unit.
It adds the unit to `Analysis.incomplete`, with a budget diagnostic when the walk recorded one.
A summary failure and a flow failure for the same function produce only one incomplete entry.
The summary pass withdraws a failed summary. Later `summaryOfFn` lookups raise its recorded failure.
A function that reads a failed summary also becomes incomplete.
An unsettled fixpoint fails the pass instead of publishing partial summaries.
A recorded budget failure never becomes a proof, a finding, or a completed unknown answer.
Only `error.AnalysisBudgetExceeded` becomes an incomplete unit.
Out-of-memory, cancellation, source-policy, syntax, and import errors still fail the whole call.

The CLI prints `zbc: incomplete` lines and exits 2 when any unit is incomplete.
Completed units retain their findings. Exit 2 takes precedence over those findings.

### Cache and scratch ownership

Each cache builds expensive derived state on first use.
Consumers share these cached results:

- `cache.fileModel()` — the FileModel, once per file.
- `cache.localBindings(proto, body)` — LocalBindings, once per fn
  body, keyed by `Ast.Node.Index`.
- `cache.summaryOfFn(...)` — the FnSummary, same key and contract.
- `cache.getLineOffsets()` — the line-start table, once per file.
- `cache.fileConstInitializer(name)` — the file-level `const`
  table, built once behind the accessor.
- the cross-file method-lookup memo, keyed by canonical declaration identity and method name.

Imported function summaries contain slices into model and summary storage.
The receiving cache deep-copies foreign summary slices and paths into its own summary arena.
The temporary foreign cache can then end without invalidating the receiving summary.
All internal summary borrows end with their owning cache.

The root `FileCache.effects_state` owns the `State` memos in `src/cache/call_summary.zig`.
Demand queries from imported documents reach this same state through `grow_state`.
The state owns completed witness sets, short-circuit verdicts, interned paths, and structural type proofs.
Memo keys include the canonical declaration, full actual context, formal parameter, and selected path.
Call-site alias and disjointness proofs stay query-local.
Cycle-dependent answers stay within their query or ownership-fold scope, not the completed-answer memo.
Recorded exhausted root demands only reproduce budget failures. They are not effect answers.
Persistent memo storage ends with `State.deinit`, normally during root-cache teardown.
The state's separate scratch arena ends after each outermost query.

The root `FileCache.return_storage_state` owns completed symbolic returns and their path bytes.
Its keys borrow canonical resolver identities. Cache teardown precedes resolver teardown.
`ExpressionLoanOptions.scratch` and the internal returned-storage `Query.scratch` borrow a `*std.heap.ArenaAllocator`.
The caller owns this arena. Query snapshots and expression-loan slices remain valid only while the arena remains alive.
Expression-loan requests retain explicit load horizons and do not cache result snapshots.
Copied-payload and written-cell witnesses are immutable snapshots owned by query scratch.
The internal `ReplayLog` in `src/cache/return_storage.zig` stores their ordered replay histories in immutable, balanced trees.
Certificates share complete subtrees or selected ranges instead of expanding repeated occurrences.
Logical length, order, and multiplicity remain unchanged, as do all per-occurrence query work charges.
The copied-payload consumer filters shared subtrees only with its pure, uncharged cell/path predicate.
It still visits every matching occurrence in order; written-cell scans retain their original charges and early exits.
`returnedStorageAt` creates a temporary scratch arena and copies returned path storage into the root state before teardown.

Ordinary calls and `@call` share `Analyser.resolveCallReturnType` in `src/type_engine/analysis.zig`.
`CallOperands` maps the bounded untyped literal tuple syntax to explicit `@call` arguments without an implicit receiver.
An unknown or opaque argument tuple leaves the return type unresolved.
Generic bindings use the actual caller's `ResolveOptions`. Resolver errors propagate instead of becoming a successful unknown result.

Returned-storage memo keys include canonical declaration identity and actual type context.
Only complete, caller-independent symbolic returns enter that memo.
Private-cell effect proofs keep constructor and call bindings query-local.
Copied-element alternatives select payloads within a formal sequence, not its backing cells.
Visible assignments and `@memcpy` retain exact copied-source witnesses, including addresses returned by helpers.
These positive witnesses do not certify disjointness or complete storage coverage.
Opaque calls and assembly still block non-retention certificates without proving an escape.

`FileCache.callEffectAt` uses `EffectSelection.whole` from `src/cache/call_summary.zig` for whole-call mutation queries.
It resolves the canonical callee or authenticates a supplied callee against the call and caller context.
Only `.read_only` proves no mutation. It proves neither returned-storage safety, loan independence, nor initialization.
Whole-only negative early exits return `.unknown` and publish no partial witness set or completed source-event plan.
Positive proofs still require complete effect coverage. Precise effect queries retain their full folds.

A scalar byte element type alone does not prove destination/header disjointness.
`@memcpy` and `@memset` require an authenticated typed destination region or actual canonical allocation/provider provenance.
Incompatible pointer-header reinterpretations and union-member overlap keep effect proofs incomplete and retain positive loans.
Distinct typed struct sibling fields remain disjoint, including byte fields.
Callback field sources require authentication. An old mutable initializer does not establish the current callback source.

The semantic witness memo remains keyed by canonical declaration, full actual context, formal parameter, and selected path.
A separate completed source-event plan uses canonical declaration and full actual context.
Only this syntax plan omits formal and path coordinates. It does not cache effect answers.
The first scan completes branch pruning and reaches EOF before publication.
Publication also requires successful witness freezing. Incomplete scans and errors publish no plan.
Replay processes every ordered call, write, and opaque event with fresh question-local frame state.
Origin, disjointness, and alias proofs remain live for each question.

Source call-effect proofs follow capture origins through the actual condition, iterable, or switch scrutinee, not the control-flow body.
Loop-backedge rebinding prevents the initial capture origin from discharging effects on formal-rooted storage.
This includes rebinding after a capture use and arguments inside call-wrapped conditions.
Undecodable opaque events retain an unknown witness.

`src/cache/return_storage.zig` traverses native array and literal tuple element payloads from their syntax.
This traversal does not establish a complete certificate for arbitrary typed tuple payloads.
An ambiguous struct initializer requires a canonical array shape and an exact element count before it proves complete array payload coverage.

When an aggregate can carry addresses, omitted defaults require address-free field proofs in the aggregate's declaring frame.
Supplied fields alone cannot establish that proof.
Expression-cycle reservations belong to one body frame and retire as each expression returns.
A live cycle keeps the origin unknown.

An immutable body shares a completed write index qualified by binding declaration, not only name.
This index shares syntax only. Token horizons, declaration filtering, and unresolved-write policy remain query-specific.
Incomplete construction and errors publish no write index.
The root `FileCache` and its per-document caches own the event, formal-use, and write-index buffers.
These buffers borrow the immutable source snapshot and the original resolver's identity arena.
Cache teardown frees the buffers before resolver teardown.

Unknown absorbs other expression origins, so traversal stops when further origins cannot change the answer.
Syntax sharing adds no negative cache and does not change analysis budgets.

Normal and error cleanup proofs share the enclosing work budget across nested callee queries.
An authenticated `noreturn` call ends both exit paths. Its implementation cannot
contribute a returned-storage cleanup certificate, so the proof does not descend
into that implementation. Unknown effects remain unknown; budget failures still
propagate for reachable cleanup paths.

Numeric proofs use checked compile-time arithmetic and the actual tag interval
of exhaustive enums. Non-exhaustive enums do not supply a closed interval.
A slice passed by value copies its header: writes through its elements do not
change the caller's length bound. A possible write through a pointer to that
header invalidates the bound. Unknown values and unresolved destination types
remain unproved, rather than being treated as safe conversions.

`IntegerDomain` and `State.scalar_values` in `src/flow/abstract_state.zig` keep type bounds separate from runtime definedness.
Type width or range cannot initialize an undefined or opaque runtime operand.
`src/flow/cfg_transfer.zig` requires defined expressions and inputs before it records scalar values.
Conversions and field payloads require operand definedness, not only a known result type.
`RuntimeOperandFilter` in `src/flow/cfg_builder.zig` separates type-only queries from runtime payload reads.
Type-only queries do not consume runtime payload.

Fixed-array selections retain a separate `ModuloIndex` certificate for `input % modulus`.
The input must be an authenticated unsigned local with a defined runtime value.
The divisor must be positive and no larger than the source array extent.
The parser accepts a constant divisor or a fixed array's `.len`, not trailing arithmetic.
Only complete source payload coverage certifies this selection.
Selected nested arrays retain both source coverage and selector dependencies. Partial payloads remain unproved.

Pattern rules use this shared-cache signature:

```zig
pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,   // shared state
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void { ... }
```

Rules that need none of it take `cache` and `_ = cache;` it.

## Shared infrastructure for pattern detectors

### `ast/tokens.zig` — token primitives

Allocation-free helpers that work on a `tags: []const Token.Tag`
slice extracted once via `tree.tokens.items(.tag)`.

Key fns:

- `matchBrace` / `matchParen` / `matchBracket` — given an opener,
  find the matching closer.
- `findStmtSemicolon` — next `;` at paren/brace/bracket depth 0.
- `skipDeferStmt` — given `defer` / `errdefer` keyword, jump past
  the entire deferred statement.
- `skipNestedFn` — given any token before a fn body, skip the
  body `{...}`.
- `skipFnDecl` — given the `fn` keyword, skip the proto `(...)`
  and body `{...}`; bails early on `;`/`,`/`fn` for extern /
  proto-only fn decls.
- `hasTokenInRange` — true iff any token in `[start, end]` has a
  given tag.
- `findIdentInScope` — find first use of a named identifier at
  brace depth 0 within a bounded scope.
- `enclosingFnDecl` — innermost fn_decl node containing a token.
- `isTrivialBody` — true iff a fn body is empty or contains only
  `_ = <expr>;` discard statements.
- `returnsType` — true iff a fn returns the literal `type` (a
  type-builder fn; skip to avoid double-scanning its inner body).
- `fnProto` / `bodyOf` — extract proto / body of an `fn_decl`
  across the four AST variants.
- `FnDeclIter` / `iterFnDecls(tree)` — iterate every fn_decl in
  the file, skipping type-builders.

Conventions:

- `last` is the **inclusive** upper bound of the scan window.
- All "find" helpers return `?TokenIndex` so the caller can
  `orelse continue`.
- Token-tag gotcha: `.?` is two tokens (`period` + `question_mark`),
  but `.*` is one token (`period_asterisk`).

### `ast/scope_iter.zig` — scope-aware iteration

- `findIdentUseInEnclosingScope` — bounded by the enclosing `}`;
  allows nested blocks inside the scope; sibling scopes with the
  same name don't match (shadow-aware).

### `model/method_names.zig` — name classifiers

Stable name-based filters used across many rules.  Centralizing
keeps "is this an allocator?" / "is this a cleanup method?"
consistent project-wide.

Classifiers:

- `isAllocatorishName` (gpa, alloc, allocator, *_alloc, *Allocator, …)
- `isSelfReceiverName` (self, this)
- `isCanonicalOutName` (result, out, r)
- `isCleanupMethodName` (deinit, free, destroy, close, stop, release, deref, unref, removeRef, finalize, dispose)
- `isAcquireMethodName` (reference, retain, addRef, …; ref excluded)
- `isReleaseMethodName` (release, deref, unref, …)
- `isAllocMethodName` (alloc, allocSentinel, dupe, dupeZ, create, …)

### `model/file_model.zig` — FileModel (TypeTable + FnTable)

Per-file semantic model, built ONCE per `Ast`.  Replaces ad-hoc
per-rule type / fn table-building.

```zig
var model = try fmodel.build(gpa, &tree);
defer model.deinit();

// Types
const ti = model.findType("Outer") orelse return;
if (ti.hasMethod("deinit")) ...
if (ti.hasCleanupMethod()) ...      // any of deinit/close/destroy/free/...
for (ti.fields) |f| ...              // f.name, f.type_first..type_last, f.has_default
for (ti.methods) |m| ...             // m.name, m.body_first, m.body_last, m.receiver

// Top-level fns (NOT methods — those live in TypeInfo.methods)
for (model.fns) |f| ...               // f.is_pub, f.returns_error_union
```

Scope (v1):

- Top-level `const Name = struct/union/enum/opaque { ... }` decls.
- Methods + best-effort struct fields within those decls.
- Top-level fn_decl nodes (NOT methods).

Out of scope (v1; add when a rule needs them):

- Nested types (struct inside struct).
- Anonymous types (`return struct { ... }`).
- extern fns / extern structs.

### `ast/token_query.zig` — token-level pattern DSL

Rules describe SHAPES instead of writing bespoke token-walk loops.
A Pattern is a sequence of `Atom`s; matching it against a token
position returns a `Match` (with captures) or null.

Atom kinds:

- `tok: TokenTag` — match one token by tag (no text check)
- `text: []const u8` / `text_at: { slot, text }` — identifier-equals
- `pred: fn` / `pred_at: { slot, pred }` — identifier-passes-pred
- `capture: u8` — capture any identifier into slot N
- `ref: u8` — match identifier whose text equals capture[N]
- `opt: [...]` — optional sub-pattern (rewind on fail)
- `any_of: [...]` — first-matching alternative wins
- `paren_args` / `bracket_args` / `brace_args` — balanced delimiter skip
- `capture_until: { slot, stops }` — token-range capture up to stop
- `ref_range: u8` — match a previously-captured token range

Combine with `findAll` / `findAllInBody` / `findInSameScope` /
`findInEnclosingScope` to express the "bind X here, find use of X
later" pattern most rules need.

The `*_at` variants exist so report sites use stable capture slots
instead of fragile `m.start + N` offsets.

### `model/model_query.zig` — AST-level (FileModel) DSL

`model_query.zig` queries FileModel types, fields, and methods with
`TypePred`, `FieldPred`, and `MethodPred`.
`ast/token_query.zig` queries token sequences instead.

The two compose: use `mq.findTypes` / `findFields` / `findMethods`
to narrow down WHICH bodies to scan, then use `query.*` to scan
those bodies for token patterns.

### `model/local_bindings.zig` — LocalBindings (per-fn binding origins)

Per-fn-body model.  For every `const NAME = <expr>` / `var NAME =
<expr>` and every fn parameter, classify the **origin**:

```zig
var bindings = try local.build(gpa, &tree, proto, body);
defer bindings.deinit();

const x = bindings.find("x") orelse return;
switch (x.origin) {
    .param        => ...,
    .literal      => ...,
    .call         => |c| ...,           // free fn call: foo()
    .method_call  => |c| ...,           // method: recv.method()
    .try_call     => |c| ...,           // try foo()
    .alias        => |other_name| ...,  // const X = Y
    .field_access => |fa| ...,          // const X = self.field
    .addr_of      => |aliased| ...,     // const X = &Y
    .index_op     => ...,               // const X = arr[i]
    else => {},
}

// Unified call accessor — strips the try / non-try distinction.
if (x.asCall()) |c| { ... c.receiver, c.method, c.paren_token ... }
```

Replaces hand-rolled one-hop aliasing chains that several rules
currently do for the few questions they need.

### `testing.zig` — rule-test API

One-line test assertions:

```zig
const testing = @import("../../testing.zig");
const check = @import("./my_rule.zig").check;
const R = "my-rule-id";

test "fires on the bug" {
    try testing.expectFires(check, R, src);   // exactly 1 problem with id R
}

test "doesn't fire on correct usage" {
    try testing.expectNoFire(check, src);     // zero problems
}

test "n sites" {
    try testing.expectCount(check, R, 3, src);
}
```

On failure each helper dumps observed problems so the first
failing test gives full context — no need for printf-recompile.

Lower-level `runRule(gpa, check, src)` + `freeProblems(gpa, &p)`
are available for tests that need raw problem inspection.

### `trace.zig` — `--trace=<rule-id>` decision log (opt-in)

Rules can emit decision events:

```zig
const trace = @import("../../trace.zig");
const R = "my-rule-id";

trace.note(R, tree, t, "matched binding via opener");
trace.skip(R, tree, t, "close is inside defer");
trace.match(R, tree, use_tok, "use after close");
trace.enter(R, tree, t, "entering body");
```

By default the calls are no-ops (one compare-and-branch).  The
user runs:

```bash
zbc --trace=fd-write-after-close path/         # one rule
zbc --trace='*' path/                           # all rules
```

… and stderr fills with `[trace:<rule-id>] <kind> @ <line:col>: <msg>`.

**Adoption is opt-in, not required.**  Most rules don't bother.  Add
trace calls when:
- The rule has multiple decision points whose interaction is hard to
  reason about from inspection.
- You're debugging a false positive / negative on a real-world corpus
  hit and want a decision log without recompile cycles.

A clean diff that adds a new rule without trace calls is fine.

## Adding a new rule

1. **Pick a name** in `kebab-case` (the rule ID) and `snake_case`
   (the file name).  E.g., `fd-write-after-close` →
   `rules/io/fd_write_after_close.zig`.

2. **Add the invariant** to `config.zig`:
   ```zig
   pub const Invariant = enum {
       ...
       my_rule_name,
   };
   pub const all_invariants: [N]Invariant = .{
       ...
       .my_rule_name,
   };
   ```
   Bump the array length.

3. **Write the rule** in `rules/<family>/<rule_name>.zig`:
   ```zig
   const std = @import("std");
   const Ast = std.zig.Ast;

   const lexer = @import("../../ast/tokens.zig");
   const scope = @import("../../ast/scope_iter.zig");
   const fmodel = @import("../../model/file_model.zig");
   const local = @import("../../model/local_bindings.zig");
   const query = @import("../../ast/token_query.zig");
   const mq = @import("../../model/model_query.zig");
   const problem = @import("../../problem.zig");
   const testing = @import("../../testing.zig");
   const config_mod = @import("../../config.zig");
   const file_cache_mod = @import("../../cache/file_cache.zig");

   const R = "my-rule-id";

   pub fn check(
       gpa: std.mem.Allocator,
       tree: *const Ast,
       cache: *file_cache_mod.FileCache,
       config: *const config_mod.Config,
       problems: *std.ArrayListUnmanaged(problem.Problem),
   ) !void {
       if (!config_mod.isEnabled(config, .my_rule_name)) return;
       _ = cache;  // delete if you use cache.localBindings / cache.fileModel
       // ... detection logic ...
   }
   ```

   For rules that walk per-fn AND need LocalBindings, use
   `lexer.forEachFnCached(gpa, tree, cache, problems, checkFn)` — the
   helper threads cache to the per-fn callback so you can call
   `cache.localBindings(proto, body)`.

4. **Add inline tests** at the bottom of the rule file using
   `testing.expectFires` / `testing.expectNoFire`.  Cover the
   canonical bug + the most likely false-positive shape +
   2-3 edge cases.

5. **Register it** in `rule_catalog.zig`:
   - `const my_rule_mod = @import("rules/<family>/my_rule_name.zig");`
   - Append `.{ .id = "my-rule-id", .check = my_rule_mod.check }` to
     `escape_detectors` (the dispatch table).
   - Append `_ = my_rule_mod;` to the test block at the bottom of
     the file (refAllDecls includes inline tests in the test binary).

   No edit to `lib.zig` needed — the dispatch loop iterates the table.

6. **Add to the rule catalog** in `rule_catalog.zig`:
   ```zig
   .{
       .id = "my-rule-id",
       .title = "<one-line summary>",
       .body = @embedFile("rules/<family>/my-rule-id.md"),
   },
   ```

7. **Write `rules/<family>/my-rule-id.md`** with the bug class, bad/good
   examples, and detection notes.  This is what `zbc --explain
   my-rule-id` prints.

8. **(Optional) Sprinkle trace calls** at decision points — `trace.skip`
   for early exits, `trace.match` for the fire point.  Most rules
   don't bother; do it when the rule has multi-stage gating you'll
   want to debug later.  See the trace section above.

9. **Sweep the corpora** to validate behavior:
   ```bash
   zig build -Doptimize=ReleaseFast
   for repo in bun mach tigerbeetle ghostty Ez; do
       count=$(./zig-out/bin/zbc /Users/ericsan/Development/OpenSource/$repo \
           2>&1 | grep -c "my-rule-id")
       echo "$repo: $count"
   done
   ```

## Build self-audit

The default build step runs zbc on `src/` and `build.zig`.
The build script supplies named-module declarations for imports such as `@import("type_engine")`.
With the default Debug mode, the audit uses a separate ReleaseSafe executable with safety checks enabled.
An explicit non-Debug optimization mode reuses the CLI executable built with that mode.
The audit passes `--allow-partial`: budget-partial files are listed on stderr but do not fail the build.
Any finding (exit 1) or failed file (exit 2) fails the build.

## Performance notes

- Use `zig build -Doptimize=ReleaseFast` for corpus sweeps.
  A Debug CLI ran about 8 times slower than ReleaseSafe on 2026-10-13: 57.7 s versus 7.3 s for
  `src/rules/misc/intfromfloat_without_clamp.zig build.zig` with `--jobs=1`.
- `main.zig` uses `std.Thread.spawn` with one session per worker.
  `--jobs=<n>` selects a positive worker limit. The default uses the CPU count, or four if that lookup fails.
  The worker count never exceeds the selected task count.
  Each worker runs on a 256 MiB stack (`type_engine.resolve_stack_bytes`; pages commit only when touched). The main thread only joins, unless no worker could start.
  The resolver stops at 256 nested node queries per analyser (`default_resolve_depth_limit`), answers unknown there, and settles no answer that rested on the cut.
- Flow and pattern rules share the original parsed AST and per-analysis `FileCache`.
  The cache builds FileModel once per file and LocalBindings once per function body.
  A session retains imported documents and models for its worker's source snapshot.
