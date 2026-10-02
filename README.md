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

## Integration branch status

This work branch requires Zig 0.16.0. Native CLI compilation, `--list-rules`,
and a one-file source-analysis smoke passed. Full current regression acceptance
is deferred; nine previously recorded regressions remain unresolved.

The default build also runs the whole-source self-audit. That audit did not
finish within 600 seconds; the install target reaches the same audit and also
timed out. To compile and exercise the CLI separately without changing the
default audit contract, use `zig build run -- --list-rules`.

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

Put the analyzed project's Zig compiler on `PATH`. The type engine runs
`zig env` to locate that compiler and its standard library. It accepts JSON
and ZON output and does not require a separate `which` executable.

## Rules

Rules in two families; `zbc --list-rules` is the current catalogue:

**Flow analysis** — must-not-escape / must-not-free-twice guarantees via
per-fn CFG and abstract interpretation:

`heap-use-after-free`, `heap-double-free`, `arena-use-after-kill`,
`arena-escape`, `stack-escape`, `use-undefined`, `allocator-mismatch`,
`interior-pointer-destroy`

**Pattern detectors** — catches recurring bug shapes from real Zig PRs:

- Heap leak / aliasing: `heap-leak`, `partial-union-write`,
  `aliased-heap-dupe`, `clobbered-by-struct-reset`, `realloc-byte-count`,
  `asymmetric-field-free`, `free-without-null-then-check`,
  `overwrite-without-deinit`
- Error-path cleanup: `missing-errdefer-between-tries`,
  `free-then-try-realloc`, `destroy-after-deinit-in-loop`,
  `dead-errdefer-in-result-fn`, `duplicate-errdefer`,
  `missing-errdefer-on-out-param`, `unreleased-refs-on-error`,
  `unreleased-factory-handle`
- Pointer / slice stability: `hashmap-getptr-rehash`,
  `arraylist-items-slice`, `fd-write-after-close`,
  `stack-fallback-escape`, `slice-of-arena-into-heap`,
  `borrowed-slice-into-out-param`,
  `borrowed-slice-into-stack-buffer-returned`,
  `memset-undef-after-len-truncation`,
  `sentinel-strip-free-size-mismatch`
- Tagged-union semantics: `tagged-union-retag-with-old-payload-read`,
  `union-deinit-without-inert-reset`, `self-undefined-after-destroy`,
  `return-borrowed-payload`
- Lifecycle / sibling consistency: `reset-skips-pooled-resource-release`,
  `missing-deinit-on-composed-owner`, `owned-field-no-outer-cleanup`,
  `deinit-order-violates-construction-dep`,
  `defer-and-errdefer-free-overlap`, `move-out-without-restore`
- Concurrency / hardening: `publish-then-touch-self`,
  `assert-on-untrusted-input`

`zbc --explain <rule-id>` prints the rationale, canonical bug, and fix.

`slice-loop-reentrant-grow` uses the actual loop body, including single-expression
bodies. Both direct methods and transitive calls account for possible aliases.
Different parameters or embedded list headers do not prove separate allocations:
a caller can pass one pointer twice or copy a header. Private storage requires a
declaration-proved fresh initializer and no publication or rebinding. Integer
field reads by value and deferred standard-list cleanup preserve that ownership;
field addresses, header copies and assignment targets do not. A direct
call through a different receiver is exempt only for the actual standard-library
single-element append and private storage; same-named project methods do not
qualify. A project member named `empty` is not the standard library's empty-list
constant.
The compiler-owned `std.mem.eql` declaration and its aliases only read their
operands, so their callers do not acquire collection-growth effects. Project
lookalikes and unresolved declarations remain conservatively charged.

`index-minus-one-without-zero-guard` follows evaluation order into `catch` and
`orelse` fallbacks. Effects of the failing operand precede the fallback; a later
fallback mutation cannot erase a guard for an earlier indexed read.

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
