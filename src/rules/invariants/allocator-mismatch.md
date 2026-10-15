# allocator-mismatch

A heap allocation is freed by a different allocator than the one
that produced it.  Under most Zig allocator implementations
(mimalloc, page-allocator, arena pools, custom GPAs) this is
undefined behavior — the freeing allocator's bookkeeping doesn't
know about the allocation, and may corrupt its own data structures
or silently leak.

## Example

Incorrect — `buf` is allocated by `mimalloc` but freed via
`default`:

    const buf = try mimalloc.alloc(u8, 32);
    // ...
    default.free(buf);                       // ← allocator mismatch

Fix — free with the same allocator that allocated:

    const buf = try mimalloc.alloc(u8, 32);
    // ...
    mimalloc.free(buf);

## When this might be a false positive

- Different local names do not by themselves prove different
  allocator values. A source-proved copy must retain the selected
  allocator identity at the allocation site. A later rebind of
  either local must not change the provider of an old allocation.
- The allocator's `free` accepts arbitrary heap pointers (e.g.
  some test harnesses route all frees through a single sink).
  zbc has no way to know this; rework the call shape so a single
  named allocator is consistent end-to-end.
- A wrapper's receiver is not necessarily its allocation provider.
  For `work.alloc(T, n)` that calls `work.plan.allocator.alloc(T, n)`,
  compare the selected allocator value with the freeing allocator,
  not `work` with the local that holds a copied allocator. The proof
  must retain the exact call declaration, contextual type, field path,
  and value at the allocation site. A later field rebind does not
  retroactively change an earlier allocation's provider.
  An unknown provider does not prove that two allocators match.
  The allocation's lifetime identity remains separate from its
  allocator provider. A wrapper result or pointer cast must not
  invent a new allocation merely to obtain a provider identity.
  Concrete local providers require an authenticated SDK allocation
  or release primitive and the canonical type of its exact allocator
  argument. A non-allocator wrapper receiver is not a provider.
  Complete provider projection through source wrappers remains an
  analysis limit: an unproved provider stays unknown, so some real
  mismatches through wrappers remain unproved. Absence of a warning
  does not prove that the providers match.


## Related

- `heap-double-free`: freeing the same pointer twice.
- `heap-use-after-free`: reading a freed pointer.
