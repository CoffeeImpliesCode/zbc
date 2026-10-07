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
- A settled short-circuit rejection keeps both negative branch facts:
  after `if (idx == 0 or idx > items.len) return`, an unsigned `idx` is
  positive. An upper-bound check alone does not exclude zero. A zero
  rejection alone does exclude underflow, but does not prove the whole
  subscript is in bounds.
- One-based counters can retain an independently verified loop-entry floor.
  The shared engine checks the complete body and backedge; a zero-based
  initializer, wrapping update, escaping counter, or conflicting body write
  does not establish that floor.
- Same-document returned slice headers carry extents proved on every
  successful return, including anonymous array literals. An empty alternate
  return removes a positive lower bound.
- Canonically resolved same-document integer-returning methods can export
  proved return floors. A propagating `try` or terminating catch reads only
  integer success values; a continuing error fallback cannot inherit a
  successful append's positive count. Constructor or accessor names alone
  do not establish an invariant.
- Mutation, address escape, wrapping arithmetic, or conflicting incoming facts can remove a positive-bound proof.
- An indexed store preserves an independent local index when the body does not
  expose that local's address. It still invalidates facts about pointer-backed
  or escaped storage that the array element can alias.
- A same-value element store can retain the loaded pointer scalar's lower bound
  only for identical, explicitly declared, naturally aligned integer parameter
  types. Unaligned storage, computed pointers, and coercions do not prove this.
- Ordinary calls cannot change a bare frame-local scalar passed by value when
  its address does not escape. Deferred cleanup still uses the same per-path
  effect checks; unrelated cleanup does not erase a pointer-root length guard.
- Successful `try std.testing.expect(condition)` records the condition.
  Imported aliases require the standard library's declaring document identity.
  A caught error or a project-defined `expect` records no success fact.
- A `clone` name or `*const` receiver alone does not prove preservation through
  nested calls. Without a complete path-effect proof, such calls can remove a
  length bound.
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
