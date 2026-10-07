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
- The RHS must mention a deferred name as an identifier
  somewhere — not necessarily as a direct argument.
- With typed analysis, copied values are not reported when the complete
  retained type graph is proved address-free. The proof reads fields in
  their declaring resolution frame, including imported types and aliases.
  Optional and array elements must also be address-free. A union is safe
  only when **every** payload is address-free; payloadless members carry
  no address. For example, `out.range = state.rangeOf("") orelse .unknown`
  is safe after `defer state.deinit()` when the returned union contains
  only numeric ranges. Adding a slice to any payload prevents that proof.
  Unknown types, pointers, and slices do not qualify. Explicit address-bit
  operations such as `@intFromPtr` also prevent this exemption.
- A write is **not** reported when a later `defer <same place> = <literal>;`
  clears it before the cleanup runs.  Defers unwind last-in-first-out, so a
  clearing defer in the cleanup's own scope and registered after it fires
  first (`defer exits.deinit(); o.capture = &exits; defer o.capture = null;`).
  The clearing defer must be registered before the write, or be the
  statement right after it (nothing can exit in between), and its value
  must be a literal (`null`, `.{}`, `&.{}`, a number or string).

## Limitations (deliberate)

- Doesn't distinguish cloning vs borrowing constructors in the
  RHS — `<out>.* = MyType.init(X)` fires whether `init` clones
  or just stores a reference.  Most `init(X)`-style calls in
  practice are non-cloning, so this is OK; cloning constructors
  produce no FP because the rule fires on the assignment but the
  semantic is benign.  Reviewer must verify.
- Doesn't track multi-hop aliasing — `const tmp = X; out.* = tmp;`
  wouldn't fire (only `X` is in deferred set, not `tmp`).
- Same-fn scope only; cross-fn defer / cleanup is out of scope.
