# intfromfloat-without-clamp

**Severity:** warning
**Category:** integer conversion / undefined behavior
**Analysis:** typed AST and shared numeric range analysis

## What this checks

The rule checks runtime `@intFromFloat` conversions.
It reports when the argument is not proved finite and within the destination integer's conversion range.
The destination comes from the conversion's context, including a return type or a parameter type. For an optional or error-union result, the conversion produces the integer payload.

NaN, infinity, and an out-of-range conversion trap in Debug and ReleaseSafe.
In unchecked builds, the operation has undefined behavior.
A warning means the analyzer did not prove safe conversion for every reachable input.

Rounding does not prove finiteness or range.
`@floor`, `@ceil`, `@round`, and `@trunc` can still produce NaN, infinity, or an out-of-range value.
A one-sided `@min` or `@max` does not establish both required bounds.

## Example (fires)

```zig
// BUG: modf.ipart can be +Inf when seconds is +Inf
const modf = std.math.modf(seconds);
interval.sec += @intFromFloat(modf.ipart);
```

```zig
// BUG: float from JS could exceed i64 range
const int: i64 = @intFromFloat(float_from_js);
```

## Fix

Check a finite domain before conversion:

```zig
fn convert(value: f64) ?u8 {
    if (!(value >= 0.0 and value < 256.0)) return null;
    return @intFromFloat(value);
}
```

This comparison also rejects NaN and both infinities.
By contrast, `if (value < 0 or value >= 256) return null;` does not reject NaN.

Use clipping only when the application permits a changed value.
The actual bounds must fit the destination, and the clipping operation's NaN behavior matters.
Converting an integer maximum to a float can round it upward; that rounded value is not a safe inclusive maximum.

## Analysis boundary

- Dominating finite comparisons, resolved arithmetic, and supported source-proved helper contracts can supply bounds.
- Trusted standard-library clipping is checked against its declaration and actual arguments. A user helper named `clamp` has no implied contract.
- Input masks and arithmetic can prove a finite result without any clipping call.
- A finite bounded floating dividend with a finite positive `@mod` divisor has a nonnegative result bounded by the divisor. An unresolved divisor or a dividend that can be NaN or infinite does not supply this proof.
- Effects are evaluated in source order. Mutation before conversion can invalidate earlier facts.
- Private generic helpers are checked in each resolved local call frame. Conversion result locations use that frame's integer payload, including explicit error-union and optional returns. Direct type-valued inline tuple loops supply one frame per tuple element, including calls inside test declarations. A merged tuple type is not a destination proof.
- An unresolved direct call with a different callee name does not block this census when the private helper's namespace is a `const` container literal bound by a statement in a local block and the complete file proves both the helper and namespace do not escape. Namespace-member, inline-literal, or instance-type transport can let an opaque helper reflect a method, so it also prevents this exclusion. Function aliases, unresolved references with the helper's name, and unknown reflective targets still prevent closing the census. Module-level namespaces stay conservative. This does not infer a range from an unresolved receiver or skip any concrete helper frame.
- Finite rejection followed by truncation and destination-specific `minInt(T)` / `maxInt(T) + 1` bounds can prove a generic conversion. The upper bound must be exclusive; range comparisons alone do not reject NaN.
- Compile-time-only expressions are not runtime conversion sites.
- Analysis budget exhaustion is incomplete analysis, not a clean result.

## Real-world instances

- oven-sh/bun#28364 — `Timer`: `modf.ipart` of a JS timer value could be
  `+Inf`; `@intFromFloat` panicked.
- oven-sh/bun#29328 — GC scheduler passed a float that exceeded `i64`
  range to `@intFromFloat`, causing a panic.
