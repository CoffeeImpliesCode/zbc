# else-literal-absorbs-addend

`base + if (COND) EXPR else 0 + ADDEND` can omit `ADDEND` when `COND` is true.
Zig parses the last addition inside the else branch, not after the conditional.

## What the rule checks

The rule uses parsed parent and branch ownership.
An addition must directly own an unparenthesized `if` expression as its right operand.
That conditional's else branch must start with `0 +` or `1 +`.

Explicit parentheses around the conditional or its else-branch sum make the grouping clear.
Standalone conditional branch arithmetic is not a candidate.
These intentional forms do not trigger:

```zig
root.len + (if (suffix.len == 0) 0 else 1 + suffix.len)
if (nullable) 0 else 1 + field_value
base + if (cond) 1 else (0 + extra)
```

Parentheses around the complete outer sum do not change the conditional's ownership.
Thus `(base + if (cond) 1 else 0 + extra)` still triggers.

## Why it matters

In Zig, `if` expressions are not statements — they produce a value — but their precedence is **lower** than arithmetic operators. So:

```zig
base + if (cond) 1 else 0 + extra
```

parses as:

```zig
base + (if (cond) 1 else (0 + extra))
```

When `cond` is true, the result is `base + 1` and `extra` is silently discarded. This is almost always a capacity-calculation bug.

## Real-world instances

- **oven-sh/bun#30466** (and 20+ duplicate PRs): `ensureTotalCapacity(defaults.len + 2 + if (allow_addons) 1 else 0 + conditions.len)` — when `allow_addons` was true (the default for `Bun.build`), `conditions.len` was dropped from the capacity request. Passing several custom conditions then caused `putAssumeCapacity` to write past the reserved slots, crashing the bundle thread.

## Fix

Parenthesize the `if` expression or use `@intFromBool`:

```zig
// Option 1: explicit parentheses
base + (if (cond) 1 else 0) + extra

// Option 2: @intFromBool
base + @intFromBool(cond) + extra
```
