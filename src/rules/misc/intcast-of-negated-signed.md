# intcast-of-negated-signed

**Severity:** warning
**Analysis:** typed AST and shared numeric range analysis

The rule checks the negation before the destination conversion.
Negating a signed integer's minimum value overflows before `@intCast` runs.
Checked builds can trap; unchecked builds have undefined behavior, not defined wrapping.

## What the rule checks

The rule finds runtime `@intCast` calls whose single argument is a unary negation,
including grouped expressions, field accesses, and arithmetic operands.
It reports unless both the negation and the destination conversion are proved in range.
Resolved constants, types, dominating guards, and supported helper contracts can provide that proof.
Compile-time-only expressions are not runtime conversion sites.
A negative-sign guard alone does not exclude the signed minimum.
Private integer-return helpers can carry their complete return domain through
pure scalar call arguments, including a comptime shift width. For example,
sign-extending a 12-bit immediate into `i32` gives `[-2048, 2047]`; negating
the negative half cannot reach the signed minimum. A full-width `i32`
decoder, an unbound width, or an incomplete return summary supplies no such
proof. A forwarded call is supported only when its arguments run no code
and carry no caller storage.

For a private helper, the analysis can join argument ranges from a closed set
of resolved direct callers. It rejects public entry points, escaped function
values, and caller arguments it cannot bound. Scaling keeps a useful range only
when the multiplication fits its source type. An exact resolved `@sizeOf`,
including a packed struct with a supported explicit integer backing type, can
provide that scale; unknown layouts do not provide a constant.

## Why it matters

The expression `-VAR` for a signed integer is only defined when `VAR != minInt(T)`.
For `i64`, `minInt(i64)` is −9,223,372,036,854,775,808.
The positive magnitude does not fit in `i64`, so negation overflows in that type.

Use `@abs(VAR)` for an unsigned magnitude; it is defined for the signed minimum too.
Then check any narrower destination separately.

## Real-world instance

- **ziglang/zig#23318** (`fmtDurationSigned`): `@as(u64, @intCast(-ns))` where `ns: i64`. If `ns == minInt(i64)`, the negation `-ns` overflows `i64` before `@intCast` runs. Fix: replaced with `@abs(ns)`.

## Fix

```zig
// Instead of (overflows when ns == minInt(i64)):
fn formatDuration(ns: i64) u64 {
    if (ns < 0) {
        return @as(u64, @intCast(-ns));
    }
    return @intCast(ns);
}

// Use @abs which handles minInt correctly:
fn formatDuration(ns: i64) u64 {
    return @abs(ns);
}
```
