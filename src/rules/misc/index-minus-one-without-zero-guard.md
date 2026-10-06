# index-minus-one-without-zero-guard

**Severity:** warning
**Category:** misc / bounds

## What this checks

The rule reports `buf[idx - 1]` when no path-sensitive positive lower bound is known for `idx`.
For an unsigned index, zero causes subtraction underflow.
Checked builds can trap. Unchecked builds do not make that index valid.

A warning means the analyzer did not prove the required lower bound.
It is not a reproduced runtime failure or a proof that the whole subscript is out of bounds.

## Example

```zig
fn previous(items: []const u8, idx: usize) u8 {
    return items[idx - 1];
}
```

## Fix

Check the lower bound before the subtraction:

```zig
fn previous(items: []const u8, idx: usize) ?u8 {
    if (idx == 0 or idx > items.len) return null;
    return items[idx - 1];
}
```

## Analysis boundary

- The rule finds runtime array-access AST nodes whose index subtracts the literal `1`.
- Shared range analysis uses dominating guards, constants, and valid path relations.
  Nearby guard text, type names, and assertions in unrelated callers are not proofs.
- Mutation, address escape, wrapping arithmetic, or conflicting incoming facts can remove a positive-bound proof.
- `catch` and `orelse` operands follow evaluation order.
  The failing operand's effects precede the fallback.
  A later fallback mutation cannot erase a guard for an earlier indexed read.
- A comparison against a length bounds that length: `i < c.len` true means
  `c.len >= i + 1`, and `i <= c.len` true means `c.len >= i`.  This holds on
  either side of the comparison, and it is what makes `while (i < c.len)`
  prove `c[c.len - 1]` safe inside the body.  The bound is only recorded when
  the other operand's sign is established, so a signed cursor of unknown sign
  proves nothing.
- Compile-time-only expressions are not runtime access sites.
- Analysis budget exhaustion is incomplete analysis, not a clean result.

## Real-world instances

- oven-sh/bun#24561: `npa_str[pi - 1]` needed a `pi == 0` guard.
- oven-sh/bun#28487: a previous-element read needed `self.current > 0` before accessing `self.items[self.current - 1]`.
