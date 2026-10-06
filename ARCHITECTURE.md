# zbc architecture

zbc is a static analyzer for Zig.  Its 113 rules fall into two
families distinguished by the analysis they require:

1. **Flow analysis** — full per-fn control-flow graph and abstract
   interpretation.  Tracks values across branches, loops, defers,
   captures, and out-params.  Used for must-not-escape /
   must-not-double-free / must-not-use-after-free guarantees.
2. **Pattern detectors** — per-fn (or per-file) token / AST walks
   over canonical bug shapes mined from open-source Zig PRs.
   Cheaper than flow analysis; targets recurring "look for this
   exact shape" classes.

Both families produce `Problem` values for the same reporter.

Those 113 rule ids are declared in three places, and the three
agree:

- `src/rule_catalog.zig:32` — `all`, the documented catalog behind
  `--list-rules` / `--explain`.  100 entries.
- `src/rule_catalog.zig:674` — `escape_detectors`, the dispatch
  table for pattern detectors.  103 entries.  Invariants emitted by
  the CFG / worklist pipeline are NOT in it.
- `src/config.zig:832` — `all_invariants: [113]Invariant`, the 113
  toggles `Config.enabled` filters on.

The first two overlap on 90 ids (100 + 103 - 90 = 113).  Ten flow
invariants appear only in `all`; the other 13 pattern rules are
dispatched but have no `Rule` entry, so `--explain` does not reach
them.

This document focuses on the pattern-detector infrastructure
(`lexer.zig` / `scope.zig` / `receiver.zig` / `model.zig` /
`local.zig` / `testing.zig` / `trace.zig`) — the shared modules
every pattern rule builds on.  See `cfg.zig` / `analyzer.zig` /
`abstract_state.zig` / `transfer.zig` for the flow-analysis side.

## File layout

```
zbc/
├── lib.zig                   — orchestrator; re-exports public API
├── main.zig                  — CLI
├── problem.zig               — Problem / Note / Pos / Severity
├── config.zig                — Config + Invariant enum
├── rule_catalog.zig          — catalog metadata (`all`) + detector dispatch (`escape_detectors`)
├── cache/file_cache.zig      — per-file shared state (see "Per-file shared state" below)
│
├── lexer.zig                 — token primitives (matchBrace, FnDeclIter, …)
├── scope.zig                 — scope-aware iterators (findIdentUseInEnclosingScope)
├── receiver.zig              — name classifiers (isAllocatorishName, …)
├── model.zig                 — FileModel: per-file TypeTable + FnTable
├── model_query.zig           — AST-level DSL: find types/fields/methods
├── local.zig                 — LocalBindings: per-fn binding-origin tracker
├── query.zig                 — token-level pattern DSL (Atom / Match / findAll)
├── testing.zig               — expectFires / expectNoFire / expectCount
├── trace.zig                 — --trace=<rule-id> decision log (opt-in)
│
├── cfg.zig                   — flow-analysis CFG builder
├── analyzer.zig              — flow-analysis dispatch
├── abstract_state.zig        — flow-analysis abstract domain
├── transfer.zig              — flow-analysis transfer functions
│
└── rules/
    ├── <rule_name>.zig       — pattern-detector implementation
    └── <rule-name>.md        — per-rule documentation
```

Files at root are imported directly by rules:

```zig
const lexer      = @import("../lexer.zig");
const scope      = @import("../scope.zig");
const fmodel     = @import("../model.zig");
const local      = @import("../local.zig");
const query      = @import("../query.zig");     // token patterns
const mq         = @import("../model_query.zig"); // AST-level queries
const testing    = @import("../testing.zig");
const trace      = @import("../trace.zig");      // optional
const file_cache_mod = @import("../cache/file_cache.zig");
```

No umbrella module.  Each module is a clean dependency.

## Per-file shared state + dispatch

`lib.zig::analyzeEscape` builds ONE `FileCache` for the file
(`src/lib.zig:75`) and owns it until the analysis returns.  Both
halves of the analyzer read that one cache: the flow loop lowers
each fn against it (`src/lib.zig:98`), and then a single
`rule_catalog_mod.runEscape(gpa, &tree, &rule_cache, config,
&problems)` call (`src/lib.zig:107`) walks `escape_detectors`
(`src/rule_catalog.zig:674`) and dispatches every pattern rule.

Ownership: the cache is created and `deinit`'d inside
`analyzeEscape`, one per call, and never crosses a thread — the
worker pool in `main.zig` runs one file per `workerLoop` pass,
each with its own.  The one cross-file structure is the
`ProjectCache` (`src/lib.zig:178`), which is process-static, so a
sibling file reached through a relative `@import("./X.zig")` is
parsed once per process instead of once per referencing file.

Everything expensive a consumer needs is memoised in that cache
and built on first use, so rules that need the same answer share
one build instead of each repeating it:

- `cache.fileModel()` — the FileModel, once per file.
- `cache.localBindings(proto, body)` — LocalBindings, once per fn
  body, keyed by `Ast.Node.Index`.
- `cache.summaryOfFn(...)` — the FnSummary, same key and contract.
- `cache.getLineOffsets()` — the line-start table, once per file.
- `cache.fileConstInitializer(name)` — the file-level `const`
  table, built once behind the accessor.
- the cross-file method-lookup memo, keyed by type and method name.

Every rule's `check` signature is the same:

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

### `lexer.zig` — token primitives

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

### `scope.zig` — scope-aware iteration

- `findIdentUseInEnclosingScope` — bounded by the enclosing `}`;
  allows nested blocks inside the scope; sibling scopes with the
  same name don't match (shadow-aware).

### `receiver.zig` — name classifiers

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

### `model.zig` — FileModel (TypeTable + FnTable)

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

### `query.zig` — token-level pattern DSL

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

### `model_query.zig` — AST-level (FileModel) DSL

Companion to query.zig.  Where query.zig matches token sequences,
model_query.zig matches entities in the FileModel — types, fields,
methods — via `TypePred` / `FieldPred` / `MethodPred`.

The two compose: use `mq.findTypes` / `findFields` / `findMethods`
to narrow down WHICH bodies to scan, then use `query.*` to scan
those bodies for token patterns.

### `local.zig` — LocalBindings (per-fn binding origins)

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
const testing = @import("../testing.zig");
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
const trace = @import("../trace.zig");
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
   `rules/fd_write_after_close.zig`.

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

3. **Write the rule** in `rules/<rule_name>.zig`:
   ```zig
   const std = @import("std");
   const Ast = std.zig.Ast;

   const lexer = @import("../lexer.zig");           // if you need token walks
   const scope = @import("../scope.zig");           // if you need scope iteration
   const fmodel = @import("../model.zig");          // if you need type/fn info
   const local = @import("../local.zig");           // if you need binding origins
   const query = @import("../query.zig");           // if your rule shape fits a token pattern
   const mq = @import("../model_query.zig");        // if you need AST-level entity queries
   const problem = @import("../problem.zig");
   const testing = @import("../testing.zig");
   const config_mod = @import("../config.zig");
   const file_cache_mod = @import("../cache/file_cache.zig");

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
   - `const my_rule_mod = @import("rules/my_rule_name.zig");`
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
       .body = @embedFile("rules/my-rule-id.md"),
   },
   ```

7. **Write `rules/my-rule-id.md`** with the bug class, bad/good
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
   Spot-check a few hits to confirm they're real (or at least
   "useful noise" — every static analyzer reports some).

## Performance notes

- `zig build -Doptimize=ReleaseFast` is essential for corpus
  sweeps.  Debug-mode runs are ~10× slower.
- The `Io.Group.concurrent` thread pool is lazy in Debug — it
  effectively runs single-threaded.  Always sweep with
  ReleaseFast.  `main.zig` uses raw `std.Thread.spawn` (one
  worker per CPU) instead, which saturates properly.
- Each rule's `check` fn runs on the parsed Ast.  Parsing the
  Ast is the dominant cost; rule checks are cheap.  FileModel
  and LocalBindings are amortized by `FileCache` — built at
  most once per file (FileModel) / once per fn body
  (LocalBindings) regardless of how many rules consume them.
