# reset-skips-pooled-resource-release

A struct exposes both `deinit` and `reset` methods.  `deinit`
calls release/free/destroy/close on owned external handles
(typically pool slots, OS handles, or other allocator-managed
resources).  The sibling `reset` either does nothing for those
handles or only zeros the struct.  Callers using `reset` to
recycle the struct leave the underlying pool / sub-allocator
slots still held → silent capacity leak.

## Why this matters

`reset` and `deinit` should be lifecycle siblings: `deinit` is
"end of life," `reset` is "back to initial state, ready for
re-use."  Either one must release all externally-owned
resources; what differs is whether the struct's own backing
storage is freed.

A `reset` that forgets to release pool slots will eventually
exhaust the pool — and because the pool's free list is the
*owning* side, the leak doesn't show up in standard `gpa.deinit()`
leak checks.  The symptom is "after N reset cycles, the pool
runs out" — far from the cause.

2 PRs in TigerBeetle alone touched this same shape
(tigerbeetle/tigerbeetle#3436, #1734), suggesting the asymmetry
is invisible during code review because deinit and reset are
often hundreds of lines apart in source.

## Canonical bug (tigerbeetle/tigerbeetle#3436)

```zig
const SegmentedArray = struct {
    nodes: []*Node,
    node_count: usize,

    pub fn deinit(self: *SegmentedArray, allocator: Allocator, node_pool: *NodePool) void {
        for (self.nodes[0..self.node_count]) |node|
            node_pool.release(node);            // releases pool slots
        allocator.free(self.nodes);
    }

    pub fn reset(self: *SegmentedArray) void {
        self.node_count = 0;                    // BUG: pool slots still held
    }
};
```

## Fix

Mirror the pool-release loop in `reset`:

```zig
pub fn reset(self: *SegmentedArray, node_pool: *NodePool) void {
    for (self.nodes[0..self.node_count]) |node|
        node_pool.release(node);
    self.node_count = 0;
}
```

## Detection boundary

The rule compares sibling `deinit` and `reset` methods.
It collects cleanup candidates and compares their receiver identifiers.
For minimal resets, a non-lifecycle method must also acquire through that receiver.
An existing cleanup in `reset` keeps the current partial-clear policy.
These policies do not prove that every reported receiver owns a pool slot.

### Backing storage is not a pool resource

A standard list of address-free observations owns its backing allocation.
Appending observations does not acquire external pool slots.
A logical reset can preserve this history or its capacity.
The host event log in `Mmio.Port` has this lifetime.

The quiet case requires all of these facts:

- The field type resolves through the actual standard import to `ArrayList`
  or `ArrayListUnmanaged`.
- The instantiated element type contains no addresses.
  Inline enums and imported enum declarations retain their actual type identity.
- The cleanup call resolves to its actual declaration through the call's canonical
  AST key: the method-access dot, not the method-name token.
- The actual receiver maps to formal zero of that call.
- The exact SDK destructor body contains only a standard allocator `free` of
  that receiver's canonical slice projection, followed by clearing that header.
- The projection's complete source body returns exactly
  `self.items.ptr[0..self.capacity]`. Both calls use their actual source frames.
- The receiver root resolves to the containing struct's parameter.

This is a certificate about the selected list storage, not about global effects
of opaque allocator callbacks. It does not convert an incomplete whole-call
summary into a successful one. Every destructor and projection statement must
match the backing-only proof; an additional call, release, rebind, or observer
refuses it. An unreadable owner, unknown element, or unresolved call also refuses it.
Analysis errors propagate instead of becoming a quiet result.
The shared query limits do not change.

A user type called `ArrayList` does not satisfy the standard-type proof.
A list of address-carrying elements does not satisfy the element proof.
An external pool release remains a resource candidate.
No field name, pool type name, or cleanup name alone proves a nonpool lifetime.

## Limits

- The rule compares the first `deinit` and first `reset` in each struct.
- The existing receiver-name and partial-clear policies remain candidate filters.
- The backing-only proof does not establish a lifetime for opaque external handles.
- This rule does not prove that every omitted cleanup is a defect.
