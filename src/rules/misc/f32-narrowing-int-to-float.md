# f32-narrowing-int-to-float

**Severity:** warning
**Category:** misc / precision
**Analysis:** typed AST and shared numeric range analysis

## What this checks

The rule checks runtime `@floatFromInt` conversions whose destination is `f32`.
It reports a conversion when the input is not proved exactly representable.
An explicit `@as(f32, ...)` and an inferred `f32` result use the same check.

Every integer from −2²⁴ through 2²⁴ is exact in `f32`.
Some larger integers are also exact, but not every integer between them is.
For example, 33,554,433 rounds to 33,554,432.
Rounding can change a later bounds comparison or offset calculation.
A warning means the required precision was not proved, not that every input rounds.

## Example (fires)

```zig
fn checkBounds(offset: usize, len: usize) bool {
    return @as(f32, @floatFromInt(offset)) < @as(f32, @floatFromInt(len));
    //     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  silent rounding for large values
}
```

## Fix

Keep bounds comparisons in integer arithmetic:

```zig
fn checkBounds(offset: usize, len: usize) bool {
    return offset < len;
}
```

If the result must be `f32`, reject values outside an exact input domain:

```zig
fn convert(value: u32) ?f32 {
    if (value > 1 << 24) return null;
    return @floatFromInt(value);
}
```

`f64` represents every integer through 2⁵³, not every `u64` or `usize` value.
Use it only when that precision is sufficient.
Clipping a value changes it; use clipping only when the application permits that change.

## Analysis boundary

- The rule reads the destination type first. A destination that resolves to `f32` is checked for exact representability. A destination that resolves to another float width is outside the `f32` exactness case. The rule does not report it. Silence for another width is not a proof of an exact conversion.
- When the destination width cannot be read, the rule does not assume `f32`. It emits a warning unless the input is proved exact in every supported float format. A destination the resolver reads as a non-float type is not reported. The warning states that the conversion exactness remains unknown. It does not claim that the conversion rounds or fails.
- A run without a typed resolver reports nothing. No finding is not a proof of exact conversion.
- A named import needs proved build-module membership. An adjacent file with the same name does not establish that destination's type.
- Resolved integer types, including indexed elements of imported slice fields, constants, masks, and dominating guards can prove exactness. A local nonnegative remainder with a positive bounded divisor retains its bound.
- The proof applies before later division or multiplication. Scaling after conversion cannot repair rounding.
- Closed private helpers use the bounds of every proven caller. An exported or unresolved caller does not prove a small input domain.
- Bounded `for` loops can preserve a local counter's exit range when its only write is one literal `+= 1` per iteration. The proof uses the iterable's range, slice endpoint, or fixed extent. Unknown iteration counts, other writes, nested loops, and escaped counters do not establish this bound.
- A tag stored separately from a wide integer payload does not prove the payload's byte range. This needs a checked tag/payload relation or a source-backed return-range certificate; an accessor's name is not such a certificate.
- Closed local generic conversions are checked in each resolved instantiation. The input mask and destination format must come from the same instance; a wide-format caller cannot certify an inexact `f32` caller. Captured container constants use that instance's bindings. Open, escaped, or unresolved instances still need a universal exactness proof.
- When every closed instance supplies a resolved destination and at least one uses `f32`, an unproved conversion gets the `f32` precision warning, not an unresolved-destination advisory. Distinct unsafe conversion sites each get a finding, even when they read the same payload.
- A float-to-integer round trip needs representability provenance, not only an integer interval. A bounded exponent returned by an unresolved helper also needs a source-backed range proof.
- Field names such as `color`, and helper names such as `clamp`, do not establish a range.
- Mutation or conflicting paths can remove a proof. Compile-time-only expressions are not runtime conversion sites.
- Analysis budget exhaustion is incomplete analysis, not a clean result.

## Real-world instances

- oven-sh/bun#30134 — CSS parser typed-array offset bounds checks used
  `@as(f32, @floatFromInt(…))`, silently rounding large offsets and bypassing
  OOB guards.
