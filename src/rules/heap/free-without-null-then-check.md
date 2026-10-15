# free-without-null-then-check

A `<allocator>.destroy(<recv>.<field>);` or `.free(<recv>.<field>);`
leaves a persistent owner slot dangling unless every reachable exit resets
the slot, retires its ownership, or consumes the owner. The rule also checks
backing access and repeated release inside cleanup functions.

The bug surfaces in two ways:

1. **Optional null-check passes a dangling non-null.**  Later code
   does `if (<recv>.<field>) |h| use(h);` — the optional check
   sees a non-null pointer (the dangling one) and proceeds to
   dereference it.  UAF in `use(h)`.

2. **`deinit` double-frees the dangling slot.**  The struct's own
   `deinit` walks its fields and frees them.  The previously-freed
   slot still holds the same dangling pointer → second free.

## Why this matters

This is the canonical "free, didn't invalidate" pattern in
long-lived structs that go through cycles of activate / use /
deactivate.  The freeing fn (named `markInactive`, `reset`,
`cancel`, `endOperation`, …) intends to release the resource and
leave the struct re-usable, but forgets that "leaving it re-usable"
requires reading the field as null/empty going forward.

5+ Bun PRs in two months touched this exact shape across different
modules — it's not a one-off; it's a recurring footgun that's
invisible until something pokes the optional check on the freed
slot.

## Canonical bug (oven-sh/bun#30148)

```zig
pub fn markInactive(self: *Self) void {
    self.gpa.destroy(self.handlers.?);
    // BUG: missing `self.handlers = null;`
}

// elsewhere:
pub fn check(self: *Self) JSValue {
    const handlers = self.handlers orelse return .js_undefined;
    if (handlers.mode != .server) ...;   // ← UAF: handlers points at freed mem
}
```

The `markInactive` fn frees the handlers pointer but leaves
`self.handlers` non-null.  The next call to `check` reads the
optional, sees a non-null value, and dereferences a dangling
pointer.

## Fix

Always pair the free with a slot reset:

```zig
pub fn markInactive(self: *Self) void {
    self.gpa.destroy(self.handlers.?);
    self.handlers = null;
}
```

For non-optional pointer-or-slice fields:

```zig
self.gpa.free(self.specifier);
self.specifier = &.{};       // empty slice — checks like `.len == 0`
                              // work and the deinit's blind free is a no-op.
```

## Why the detector is precise

- Keeps the shipped destructor-entry policy: prefixes `deinit`, `destroy`,
  `finalize`, `dispose`, `take`, `consume`, `into`, `free`; exact `close`;
  and substrings `Deinit`, `Destroy`, `Cleanup`, `Finalize`, `Dispose`.
  This policy excludes stale headers at cleanup exit. It does **not**
  certify safety or hide in-body backing access, repeated release, or a
  fallible replacement that exits with a dangling owner.
- Skips comptime type-builder functions and deferred release registrations.
  Deferred actions execute in their cleanup domain, not at registration.
- Keeps the narrow `self.field` / `this.field` receiver shape. Authenticated
  allocator declarations do not depend on the allocator variable's name.
  Unresolved receivers retain the existing allocator-handle spelling filter;
  no new names are accepted. A source-resolved project method is harmless
  only with a complete whole-call read-only proof.
- Resolves member calls through the AST field-access token (`.`), not the
  method-name token used for the diagnostic. Missing type information does
  not turn a syntactic release into a safe no-op.
- Requires reset on every path, including every switch arm and both results
  of a conditional or `catch` replacement. A reset only in a catch handler
  leaves the success path unchanged; a fresh value assigned through `try`
  does not cover failure. Registered cleanup runs in reverse order on the
  applicable exits.
- Distinguishes a copied slice's `.len` metadata from backing access.
  Resetting the owner header does not repair a slice copied before release.
  A plain, non-sentinel slice with length zero cannot be released again
  through that header; reading its stale `.ptr` remains invalid.
- Credits boolean ownership retirement only when all affected paths retire
  the owner and the consumers are guarded or consume it. Atomic retirement
  requires the authenticated standard-library `swap` declaration.
- Caller consumption requires a closed, declaration-bound caller census.
  Public one-shot APIs do not gain a closed-world certificate merely from
  their current local callers. A local copied header, an enclosing owner
  release, or canonical list-backing cleanup must consume the actual owner,
  without an intervening backing use or a retained copy.

These proofs are conservative. Unknown call effects or escaping owners do
not count as safe. Source, allocation and analysis-budget errors propagate.

## Related rules

- [`heap-use-after-free`](heap-use-after-free.md) — finds the USE
  site after a free; this rule fires at the FREE site so the bug
  is caught even before the use is written.
- [`free-then-try-realloc`](free-then-try-realloc.md) — specifically
  about a fallible re-allocation that may leave the slot dangling
  on error.
- [`overwrite-without-deinit`](overwrite-without-deinit.md) — the
  dual: overwriting a slot WITHOUT freeing the prior value.
