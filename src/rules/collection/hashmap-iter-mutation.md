# hashmap-iter-mutation

Structural changes to a `HashMap` can invalidate an active `iterator()`,
`keyIterator()`, or `valueIterator()`. New entries, removals, and backing
storage changes can make its cursor stale. A value-only replacement of an
existing key does not itself change occupancy or backing storage.

## Why this matters

Zig's `HashMap` uses open addressing.  The iterator stores a numeric
cursor into the backing array.  Any mutation that changes the load
factor — adding or removing entries — may shift or tombstone slots,
making the cursor stale.  Unlike a `std.ArrayList` where a realloc
is required before items move (so no-realloc ops are safe), even a
`remove` on a HashMap can silently corrupt an active iterator.

The failure mode is non-deterministic and load-factor-dependent,
making it very hard to reproduce from a test suite.

## Canonical bug

```zig
var iter = map.iterator();
while (iter.next()) |entry| {
    if (shouldRemove(entry.value_ptr.*)) {
        _ = map.remove(entry.key_ptr.*);  // ← invalidates iter
    }
}
```

## Fix

Collect the keys to remove in a separate list, then remove after
the loop completes:

```zig
var to_remove = std.ArrayList(K).init(allocator);
defer to_remove.deinit();

var iter = map.iterator();
while (iter.next()) |entry| {
    if (shouldRemove(entry.value_ptr.*)) {
        try to_remove.append(entry.key_ptr.*);
    }
}
for (to_remove.items) |key| {
    _ = map.remove(key);
}
```

Or convert to a snapshot first (`map.keys()` / `map.values()`).

## Detection

Per-function token walk:

1. Find `const/var <iter> = <recv>.<iter-method>()` where
   `iter-method ∈ {iterator, keyIterator, valueIterator}`.
   The receiver can be a bare name or one field of a receiver.
2. Scan forward for `while (<iter>.next()) [|...|]` loop headers.
3. Inside the while body, scan for `<recv>.<mutate>(` at the same
   lexical depth (nested blocks are skipped).
4. Exclude a source-proven value-only replacement. Report the remaining mutation.

Mutate methods: `put`, `putAssumeCapacity`, `putNoClobber`,
`putNoClobberAssumeCapacity`, `remove`, `removeByPtr`, `fetchPut`,
`fetchRemove`, `swapRemove`, `clearAndFree`, `clearRetainingCapacity`,
`ensureTotalCapacity`, `ensureUnusedCapacity`, and `rehash`.

## Stable current-key replacement

The rule can exclude `putAssumeCapacity` when all these facts hold:

- The iterator, its `next` call, and the replacement resolve to the actual
  SDK hash-map declarations.
- The map has an integer key and the SDK `AutoContext` for that same key
  type. Generic bindings use the factory parameter's token and declaring
  document together. A custom hash or equality callback cannot use this proof.
- The exact formal-to-actual mapping identifies the replacement key.
  Managed and unmanaged Zig 0.16 maps both take `key` and `value` here;
  the assumed-capacity call does not take an allocator.
  The key is `entry.key_ptr.*` from this loop's current entry.
- Both receiver expressions refer to the same lexical binding.
- The complete relevant syntax contains no other call, store, rebind, or
  opaque effect. This includes replacement arguments and the rest of the loop.

The assumed-capacity contract prevents growth. The unchanged current key
proves that the entry already exists. Together, these facts prove a value-only
replacement. The method spelling alone proves neither fact.

Ordinary `put` can grow before it searches for an existing key. It remains
a candidate even when its argument is `entry.key_ptr.*`.
No-clobber insertion, arbitrary keys, custom methods, unresolved types, and
incomplete effect proofs also retain the warning.
