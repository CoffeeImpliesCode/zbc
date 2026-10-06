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

```sh
zig fetch --save https://github.com/ericsssan/zbc/archive/refs/tags/v0.1.0.tar.gz
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

## CLI

For standalone use:

```sh
zig build -Doptimize=ReleaseFast
zbc src/
zbc --format=compact src/   # grep-friendly
zbc --list-rules
zbc --explain <rule-id>
```

Exit 0 if clean, 1 if problems found.

## Rules

113 rules in two families, distinguished by the analysis each needs:

**Flow analysis** — must-not-escape / must-not-free-twice guarantees
via a per-fn CFG and abstract interpretation.  Ten invariants:
`allocator-mismatch`, `arena-escape`, `arena-use-after-kill`,
`heap-double-free`, `heap-leak`, `heap-use-after-free`,
`interior-pointer-destroy`, `partial-union-write`, `stack-escape`,
`use-undefined`.

**Pattern detectors** — per-fn or per-file token / AST walks over
canonical bug shapes mined from open-source Zig PRs.  The other 103.
Cheaper than flow analysis; each targets a recurring "look for this
exact shape" class — heap lifetime, error-path cleanup, pointer and
slice stability, tagged-union semantics, lifecycle consistency,
concurrency, and numeric / bounds bugs.

That split is not maintained here.  The authoritative lists are the
`all` catalog and the `escape_detectors` dispatch table in
`src/rule_catalog.zig`; `zbc --list-rules` prints the catalog and
`zbc --explain <rule-id>` prints one rule's rationale, canonical bug,
and fix.  ARCHITECTURE.md traces both declarations.

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
