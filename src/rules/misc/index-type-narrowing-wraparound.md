# index-type-narrowing-wraparound

**Severity:** warning
**Analysis:** typed AST and shared numeric range analysis

The rule checks two runtime `@intCast` shapes:

- The input reads a collection's `.len`.
- The converted value reaches a collection subscript, directly or through a local binding.

It reports when the input is not proved to fit the destination integer at the cast.
A warning identifies a missing range proof, not a proved out-of-range input.
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

// FIX: keep the length in usize; subtract only after a nonzero check.
var i: usize = decoded_pathname.len;
while (i > 0) {
    i -= 1;
    if (decoded_pathname[i] == '/') break;
}
```

The historical example is oven-sh/bun#31129: a `url_path` scanner used
`i16` for a reverse-scan index on paths that could exceed its range.

## When this might be a false positive

The rule reports either input shape when the analyzer cannot prove a sufficient destination range.
An out-of-range `@intCast` traps in Debug and ReleaseSafe.
In unchecked builds it has undefined behavior, not defined wrapping.

A collection's capacity can bound the input through a guard before the cast.
A subscript after the cast cannot prove that the earlier conversion was safe.
The indexed collection's reported capacity is context, not a range proof.

- **Bounded domain**: a fixed array length, a dominating guard, or a resolved
  clipping bound can prove that the cast fits. The analyzer uses the actual
  bound and destination range, not the name of a constant.

- **Other integer uses**: a cast with no `.len` input and no collection
  subscript use is outside this rule. A mask after conversion cannot prove
  that the conversion itself was in range.

## Analysis boundary

- **The destination is the context's type.** Zig supplies the type for
  `@intCast(x)`. The analyzer follows `@as`, function parameters, aggregate
  fields, returns, assignments, and arithmetic compound assignments.
  Optional and error-union destinations use their integer payload.
  A proved source domain that fits the destination needs no length guard.
  Shift compound assignments do not use the left operand's type for the right operand.
- **A bound is only kept while nothing reachable can WRITE the storage it was
  read from.**  `catch` / `orelse` handlers, `defer` / `errdefer` bodies and
  assignments are scanned for the calls and direct writes they contain; a
  handler handed a slice value, a by-value argument, or an unrelated field
  write does not end the bound. A proved fresh `std.mem.Allocator.create`
  result cannot alias pre-existing storage. Writes to that allocation still
  invalidate facts through its aliases. Unknown factories and unmodeled
  write targets remain conservative.
  The analyzer checks each field separately.
  A writable aggregate root does not erase a field bound when canonical call effects prove that field unchanged.
- **Fresh storage does not imply a read-only allocation call.** An allocator
  can invoke caller-provided callbacks. If their targets are unresolved,
  the analyzer cannot prove they leave globally reachable collection headers
  unchanged. Such a call can end an earlier field-length bound even when the
  allocation result is fresh.
  A copied, unescaped local length can retain its own guard across that call.
  Cast that same snapshot afterward; reading the mutable header again does
  not use the snapshot's proof.
- **A bound comes from a dominating guard, a compile-time value, or a
  resolved type.** The analyzer also uses these contracts:
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
  - **From a static extent.** Array literals, strings, and fixed arrays
    retain their lengths through immutable local aliases.
    Closed private callers can supply these extents to slice parameters.
    A relative literal `@embedFile` can supply an exact file size.
    The defining source path and source policy must admit that file.
    Unsupported paths and unresolved module identities prove nothing.
    Metadata I/O failures stop the query and do not create a memoized absence.
  - **From a successful helper.** A propagated `try` can retain bounds
    that hold on every successful callee exit.
    A checked constant-offset relation can transfer the bound to its source.
    A capped direct unsigned checked sum bounds each nonnegative component.
    Components receive upper bounds only, not lower bounds or nonzero facts.
    Changes to the result or either input end the relation.
    A continuing error handler does not receive the success contract.
  - **From returned slice fields.** Resolved by-value aggregate returns
    retain field extents that hold on every successful return.
    A single-label by-value union capture can select the corresponding projection.
    Unknown, omitted, or oversized alternate fields prevent a narrow bound.
    Bare slice returns can use exact argument-length snapshots.
    A stable bare boolean selector can retain a conditional extent.
    Changes to the header or selector end that conditional relation.
  - **From integer operations.** A nonnegative integer modulo a positive
    bounded divisor has a bounded remainder.
    The toolchain's unsigned `log2_int_ceil` result does not exceed its input type's bit width.

The analyzer does not assume that an unresolved `.len` field has type `usize`.
It does not infer cumulative list growth from a separate preflight loop.
Checked arithmetic wrappers need a separate relation proof.
Receiver-owned optional event headers require a distinct storage and copy proof.
An opaque source or destination remains unproved until exact type or range evidence exists.

- To suppress on a specific line:

```zig
var i: i16 = @intCast(arr.len) - 1;  // zbc-disable-line:index-type-narrowing-wraparound
```
