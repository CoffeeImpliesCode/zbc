# sentinel-strip-free-size-mismatch

`<alloc>.free(<X>.ptr[0..<X>.len])` (or `<X>.ptr.?[0..<X>.len]`)
hand-rolls a `[]u8` slice from a many-item-pointer.  If `<X>` is
a sentinel-terminated slice (`[:0]const u8` produced by `dupeZ`,
`allocSentinel`, string literals like `"hello"`, etc.) the
underlying allocation is `len + 1` bytes — but the freed slice is
only `len` bytes.  The allocator's free-size check trips with
"Allocation size N+1 does not match free size N."

A plain `[*]T` pointer has no sentinel byte to strip. Reconstructing
the original allocation extent from a record's pointer and length is
valid; the record itself cannot be passed to `Allocator.free`.

## Canonical bug (ghostty-org/ghostty#8886)

```zig
// src/main_c.zig — ghostty_string_free
pub export fn ghostty_string_free(str: ghostty_string_s) void {
    state.alloc.free(str.ptr.?[0..str.len]);
    // Trips: "Allocation size 41 bytes does not match free size 40"
    // because str was produced as [:0]const u8 with underlying
    // allocation len+1.
}
```

## Fix

Either pass the slice directly:

```zig
state.alloc.free(str);
```

or preserve the sentinel in the slice expression:

```zig
state.alloc.free(str.ptr.?[0..str.len :0]);
```

## Why the detector is precise

- Pattern is exact: `<alloc>.free(<X>.ptr[0..<X>.len])` or
  `<X>.ptr.?[0..<X>.len]`.  Both ident occurrences of `<X>`
  must match.
- `<alloc>.free(slice)` and `<alloc>.free(slice[0..N])` (without
  `.ptr`) are NOT flagged — only the `.ptr[...]` reconstruction
  shape, which is the canonical sentinel-strip footgun.
- An optional-pointer unwrap (`.?`) is included in the matched shape.
- With the type engine, the exact `<X>.ptr` expression supplies the
  canonical pointer type. Type aliases, imported declarations, optional
  pointers, and `for` element captures use that same classification.
  A known non-sentinel many-item pointer does not report.
- An outer slice's pointer is classified independently of fields in its
  element type. `[]Entry` has a non-sentinel `[*]Entry` pointer even when
  `Entry.ptr` is sentinel-terminated.
- Without the type engine, the existing declared-field model can prove
  a parameter record's plain `[*]T` field. It does not reinterpret a
  slice as its element record. Unknown classifications retain the warning;
  type-query failures propagate.

## Limitations (deliberate)

- This rule does not prove arbitrary allocation-length equality. Its
  warning concerns loss of a sentinel extent, not every possible incorrect
  slice length. For example, a record containing `[*]u8` from
  `alignedAlloc(u8, alignment, count)` and `len = count` has no sentinel
  mismatch when freed with `ptr[0..len]`.
- Multi-segment receivers (`outer.inner.ptr[0..outer.inner.len]`)
  are out of scope — the rule requires single-identifier `<X>`.
