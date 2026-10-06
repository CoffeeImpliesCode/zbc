# divmod-by-len-without-nonempty-guard

**Severity:** error
**Category:** misc / division by zero
**Tier:** semantic (value-range oracle + type engine)

## What this checks

The rule checks integer division by a container length — `x / c.len` —
where the container is not proved non-empty. Division by zero can panic
in Debug and ReleaseSafe; unchecked builds have undefined behavior.

```zig
const avg = total / items.len;     // panics when items is empty
```

## Why a semantics-first rule

Firing on every `/ c.len` would be unusable: most such divisions are over
provably non-empty containers (fixed-size arrays, slices guarded by a prior
emptiness check). This rule only fires when it **cannot prove** the container
is non-empty, using two sound queries:

- **value-range oracle** — a dominating guard establishes non-emptiness:
  `if (c.len > 0)`, `if (c.len != 0)`, `if (c.len == 0) return`, or a
  length snapshot `const n = c.len; if (n > 0)`.
  A non-empty iterable, or a supported product-count loop relation, can
  prove that a length factor is nonzero while the loop body runs.
- **type engine** — `c` is a fixed array `[N]T` with `N >= 1`, so `c.len` is a
  non-zero compile-time constant.

## Examples

Fires:

```zig
fn average(items: []const u32, total: u32) u32 {
    return total / items.len;   // items may be empty
}
```

Does not fire (guarded):

```zig
fn average(items: []const u32, total: u32) u32 {
    if (items.len == 0) return 0;
    return total / items.len;
}
```

Does not fire (fixed-size array — length is a non-zero constant):

```zig
const channels = [_]Channel{ .red, .green, .blue };
fn pick(i: usize) Channel {
    return channels[i % channels.len];
}
```

## Fix

Guard the divisor, or prove the container is non-empty before dividing:

```zig
if (items.len == 0) return error.Empty;
const avg = total / items.len;
```

## Scope

The divisor must be exactly `<path>.len` immediately after a binary `/`.
The rule does not check `%`, `/=`, grouped divisors, or arithmetic divisors.
Those exclusions are analysis boundaries, not proofs that the operations are safe.
A grouped divisor such as `/ (c.len)` can still divide by zero.

The non-empty proof must apply at the division site.
Mutation or address escape can invalidate a prior length fact.
A product-count proof must name this divisor's factor; an unrelated product does not prove it nonzero.
Analysis budget exhaustion is incomplete analysis, not a clean result.
