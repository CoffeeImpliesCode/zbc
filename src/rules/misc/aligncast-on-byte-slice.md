# aligncast-on-byte-slice

`@alignCast(expr.ptr)` — asserting alignment on a raw byte-slice pointer is unsafe. For network buffers, memory-mapped files, and serialised binary data the pointer offset is arbitrary; the runtime alignment check in `@alignCast` panics in safe builds when the offset is not a multiple of the target alignment.

## What the rule checks

The rule fires on two forms:

- **Form A**: `@alignCast(identifier.ptr)` — direct alignment assertion on a `.ptr` field
- **Form B**: `@alignCast(@constCast(identifier.ptr))` — constCast then alignCast on a `.ptr` field

`@ptrCast(@alignCast(expr.ptr))` also contains Form A or B as a sub-expression and fires.

## Suppressions

The rule is quiet when the cast is provably safe:

- **An explicitly aligned receiver** — `recv: []align(N) u8`, or a buffer
  from `alignedAlloc`, is aligned by construction.
- **A non-byte slice** — `[]u32`, `[]Struct`, … is already wider than one
  byte, so `.ptr` is not the bug class this rule names.
- **A guarded allocator context.** Recovering an allocator back out of its
  `ptr` (`@ptrCast(@alignCast(alloc.ptr))`) is safe only after a vtable
  check that dominates the cast:

  ```zig
  if (alloc.vtable != &AccountAllocator.vtable) return false;
  const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
  ```

  The receiver type must resolve to the real `std.mem.Allocator`.
  Direct `@import("std")` expressions and `const` namespace or type aliases
  can establish this identity. The rule follows each alias in its declaring
  scope. A caller-chosen `std` parameter or a custom allocator namespace
  does not establish the standard-library identity.

  The guard must share the cast's block and compare against the cast
  target's declaration. Nothing between them may rebind or escape the
  allocator. A helper can replace the inline guard only when the call
  resolves to that helper's declaration. That helper must return `bool`,
  take the allocator first, and return `false` for a vtable mismatch.
  A same-named function, an unresolved call target, or a caller-supplied
  function value cannot supply another declaration's proof.

  The block structure is resolved by a fixed 128-entry brace stack. Code
  nested deeper than that yields an **unknown** scope, not "outside any
  block": a guard whose scope cannot be determined is refused, so deep nesting
  reports rather than silently suppressing.

## Why it matters

In Zig, `.ptr` on a `[]const u8` slice returns a raw `[*]const u8` pointer whose alignment depends on where the data came from — the allocator, memory-mapping offset, or network socket buffer position. There is no guarantee it is aligned to anything other than `align(1)`.

`@alignCast(ptr)` inserts a runtime assertion that the pointer satisfies the target type's alignment requirement. For a `*Header` with 4-byte fields, that means the pointer address must be divisible by 4. Network packets can arrive at any offset; `@memcpy` into a newly-allocated buffer starts at any offset within an arena page.

The panic is non-deterministic: it depends on the alignment of the allocator's current free pointer, which varies by run and by the size of preceding allocations.

## Real-world instances

- **oven-sh/bun#27082** (Postgres binary arrays): `@ptrCast(@alignCast(@constCast(bytes.ptr)))` on network-received packet data; panicked non-deterministically on odd-offset packets.
- **oven-sh/bun#27281** (sourcemap deserialisation): `@ptrCast(@alignCast(raw.ptr))` on a memory-mapped file; panicked on unaligned mmap regions.
- **oven-sh/bun#27384** (tagged-pointer sockets): `@alignCast(data.ptr)` into a tagged-pointer arena.
- **oven-sh/bun#27290** (HTTP response parsing): `@alignCast(@constCast(bytes.ptr))` on response buffers.

## Fix

```zig
// Instead of overlaying a struct on a byte slice:
const header: *Header = @ptrCast(@alignCast(bytes.ptr));

// Use readInt for integer fields:
const magic = std.mem.readInt(u32, bytes[0..4], .big);

// Or copy into a local aligned struct:
var header: Header = undefined;
@memcpy(std.mem.asBytes(&header), bytes[0..@sizeOf(Header)]);
```
