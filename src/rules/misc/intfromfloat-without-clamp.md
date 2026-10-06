# intfromfloat-without-clamp

**Severity:** warning
**Category:** integer conversion / undefined behavior
**Analysis:** typed AST and shared numeric range analysis

## What this checks

The rule checks runtime `@intFromFloat` conversions.
It reports when the argument is not proved finite and within the destination integer's conversion range.
The destination comes from the conversion's context, including a return type or a parameter type.

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
- Effects are evaluated in source order. Mutation before conversion can invalidate earlier facts.
- Compile-time-only expressions are not runtime conversion sites.
- Analysis budget exhaustion is incomplete analysis, not a clean result.

## Real-world instances

- oven-sh/bun#28364 — `Timer`: `modf.ipart` of a JS timer value could be
  `+Inf`; `@intFromFloat` panicked.
- oven-sh/bun#29328 — GC scheduler passed a float that exceeded `i64`
  range to `@intFromFloat`, causing a panic.
