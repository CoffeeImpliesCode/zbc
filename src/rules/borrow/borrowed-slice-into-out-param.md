# borrowed-slice-into-out-param

`defer <X>.deinit()` (or `defer <alloc>.free(<X>)`) registers
cleanup for a local buffer / arena.  A later write
`<out>.* = ...<X>...` (or `<out>.<field> = ...<X>...`) where
`<out>` is a pointer-typed fn parameter pushes a view of `<X>`
into a caller-visible out-param.  When the defer fires on
function return, the out-param holds a dangling slice.

## Canonical bug (oven-sh/bun#30151)

```zig
pub fn parsePathOrSpecifier(query_string: *ZigString, ...) !void {
    var specifier_utf8 = bun_string.toUTF8(allocator);
    defer specifier_utf8.deinit();
    // ... parse result.query_string from specifier_utf8 ...
    query_string.* = ZigString.init(result.query_string);
    // ← result.query_string is a slice into specifier_utf8's bytes;
    //   defer fires on return → query_string dangles.
}
```

## Fix

Clone with the caller's allocator before assigning:

```zig
query_string.* = ZigString.init(try alloc.dupe(u8, result.query_string));
```

## Why the detector is precise

- The out-param must be a **pointer-typed parameter** (`*T`,
  `?*T`).  Value-typed parameters can't be modified by the caller
  anyway.
- The defer must be one of:
  - `defer <X>.deinit()` / `defer <X>.deinit(...)`
  - `defer <X>.close()`
  - `defer <alloc>.free(<X>)` (where `<X>` is the freed thing)
- The write must be at the top-level statement form:
  - `<out>.* = <RHS>` (deref-write through pointer)
  - `<out>.<field> = <RHS>` (field assignment through pointer)
- The shared expression-loan query follows exact local declarations, aliases,
  selected fields, and canonical call returns. An identifier spelling is not a loan proof.
- Only proved loans cause findings. Unknown types, opaque callees, and incomplete
  graph traversal add no definite lifetime violation.
- Copied address-free values carry no storage loan. This includes scalar-only
  optional, array, struct, and union payloads. Explicit address bits still carry provenance.
- A retained pointer field also needs source-proved release of that payload.
  A no-op destructor or cleanup of a different sibling field does not suffice.
  An unchanged literal can connect selected metadata to the same private scalar buffer
  that another field releases. A copied whole aggregate includes its released children.
- Release proof checks both the selected payload and the released alias for rebinding.
  A later-registered defer that replaces the payload runs before the cleanup,
  even when registered before publication. An earlier-registered replacement
  runs after that cleanup and does not keep the published payload live.
  Completed inner normal defers also run before an outer cleanup.
  Errdefer interference is checked within its own scope, after publication.
  Normal exhaustion and normal breaks do not execute errdefer, even when the
  break value is an error. A later outer error does not run a completed inner
  scope's errdefers.
- SDK identity comes from the canonical declaration, not method names.
  An allocation through a local arena's allocator factory retains that arena's lifetime.
  An allocation through its parent allocator does not. Copying an empty arena header
  does not prove that its incoming allocator dies.
- Publication RHS calls are checked for effects on their own path. A by-value
  slice argument is not its mutable source header, but a receiver may still
  rebind the selected payload before the out-param assignment. Unproved
  pointer-bearing aggregates remain conservative; unrelated scalar writes do
  not discharge a retained payload.

- A write is **not** reported when a later `defer <same place> = <literal>;`
  clears it before the cleanup runs.  Defers unwind last-in-first-out, so a
  clearing defer in the cleanup's own scope and registered after it fires
  first (`defer exits.deinit(); o.capture = &exits; defer o.capture = null;`).
  The clearing defer must be registered before the write, or be the
  statement right after it (nothing can exit in between), and its value
  must be a literal (`null`, `.{}`, `&.{}`, a number or string).

## Limitations

- The detector selects deferred cleanup in the same function and lexical scope.
  It can follow called helpers, but it does not invent cleanup for another invocation.
- Unknown release, mutable alias, or graph evidence can prevent a finding.
  An absent finding is not a complete lifetime-safety proof.
- Source errors remain strict. Budget exhaustion marks the rule incomplete.
  It does not produce a definite lifetime finding.

