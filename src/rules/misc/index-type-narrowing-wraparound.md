# index-type-narrowing-wraparound

**Severity:** warning
**Analysis:** typed AST and shared numeric range analysis

The rule checks runtime `@intCast` calls whose input reads a collection's `.len`.
It reports when the input is not proved to fit the destination integer.
Signed and unsigned destinations use the same range requirement.
An out-of-range `@intCast` traps in Debug and ReleaseSafe.
In unchecked builds it has undefined behavior, not defined wrapping.

## Example

```zig
// BUG: i16 can represent at most 32 767. A longer path makes this
// conversion out of range before the reverse scan starts.
var i: i16 = @intCast(decoded_pathname.len) - 1;
while (i >= 0) : (i -= 1) {
    if (decoded_pathname[@intCast(i)] == '/') break;
}

// FIX: use usize (or at minimum i64 for 64-bit systems):
var i: usize = decoded_pathname.len;
while (i > 0) {
    i -= 1;
    if (decoded_pathname[i] == '/') break;
}
```

The historical example is oven-sh/bun#31129: a `url_path` scanner used
`i16` for a reverse-scan index on paths that could exceed its range.

## When this might be a false positive

The rule fires on `@intCast` of a value that reads a collection's `.len`,
when no range proved for that value is known to fit the destination integer.
An out-of-range `@intCast` traps in Debug and ReleaseSafe; in an unchecked
build it is undefined behaviour rather than defined wrapping.

- **Bounded domain**: a fixed array length, a dominating guard, or a resolved
  clipping bound can prove that the cast fits. The analyzer uses the actual
  bound and destination range, not the name of a constant.

- **Bit-manipulation usage**: a variable typed `i16` that is only ever ANDed
  with a mask (`& 0xFF`) is not an index at all.  The rule fires only when the
  `@intCast` argument reads a `.len`, so pure bit-manipulation patterns do not
  trigger.

## Analysis boundary

- **The destination is the context's type.**  `@intCast(x)` has no type of
  its own; Zig gives it the type of wherever it is written.  A cast in
  argument position is checked against the parameter it is passed as, so a
  `u64` parameter accepts a `usize` length and a `u32` parameter does not.
- **A bound is only kept while nothing reachable can WRITE the storage it was
  read from.**  `catch` / `orelse` handlers, `defer` / `errdefer` bodies and
  assignments are scanned for the calls and direct writes they contain; a
  handler handed a slice value, a by-value argument, or an unrelated field
  write does not end the bound.  A write whose target cannot be named — a
  deref, a subscript, a destructure — still ends it.
- **A bound is proved from a dominating guard, a compile-time value, or a
  resolved type**, and from these four contracts:
  - **Across a call.**  A fact about the storage a pointer parameter names
    travels between caller and callee: the ceiling the caller writes on the
    receiver (`builder.options.max_text_bytes = min(.., maxInt(u32))`) is
    available inside the method, and the ceiling the method enforces on the
    way out (`bytes.len > max_text_bytes -| arena.len`) is available at
    every call site where the output contract applies.
    Input contracts require agreement across all accepted callers.
    Deferred effects can withhold an output contract.
    A subtraction alone does not prove the order of its operands.
  - **From a compile-time audit.**  `comptime { for (TABLE) |e| if (LIMIT <
    e.f.len) @compileError(..); }` proves `e.f.len <= LIMIT` for every
    element, which is how a generated table's elements get a width at all.
    An audit a `break`, a second loop or a conditional of its own could step
    over is not read.
  - **From a sub-slice.**  `s[a..b].len` never exceeds `s.len`, so a bounded
    input bounds every span cut from it.
  - **Through a name the file gives a compile-time integer.**  `const
    max_u32 = std.math.maxInt(u32);` is resolved through its binding, so a
    comparison against the name proves what a comparison against the
    expression would.
- To suppress on a specific line:

```zig
var i: i16 = @intCast(arr.len) - 1;  // zbc-disable-line:index-type-narrowing-wraparound
```
