# aligncast-on-optional-unwrap

`@alignCast(x.?)` — combining a forced optional unwrap with an alignment assertion in the same `@alignCast` call. If `x` is null the forced `.?` panics; if non-null the subsequent alignment check may also panic on unaligned data.

## What the rule checks

The rule fires on the 6-token pattern `@alignCast ( identifier . ? )` — any `@alignCast` call whose single argument is an optional forced-unwrapped with `.?`.

It does not fire when:
- The pointer is non-optional: `@alignCast(ctx)` — no `.?` involved
- The optional is guarded before casting: `@alignCast(ctx orelse return)` — the guard is not inside the `@alignCast` argument
- A same-block `if (pointer == null) return ...` dominates the cast, the
  parameter's ordinary typed pointee matches the destination, and nothing
  reassigns or escapes the pointer. A null check does not establish stronger
  alignment for an opaque or explicitly underaligned pointer.

A callback signature alone is not a proof that its argument is non-null or
aligned. Callback recovery is quiet only when closed function-pointer uses
and their paired context establish a non-null address aligned for the cast
target. Guards in possible callers alone do not establish this contract;
unresolved indirect-call provenance remains a finding.

The closed-pair proof follows resolved by-value source dispatchers across
files and immutable callback aggregates returned by private source factories.
Each use of the returned aggregate must preserve the callback/context pair.
The proof also follows nested copies, dominated local field stores, and exact
indexed cells through source-closed pointer dispatchers. Optional payload
captures preserve the same callback/context pair. A rebound index does not.

A direct source-resolved call is also closed when every use of its callback
parameter is an immediate invocation, each invocation uses the same unchanged
context parameter, and the call site supplies an ordinary typed address. This
proof is specific to that callable/context pair, including imported or generic
dispatchers. It establishes alignment only; it does not establish object
lifetime.

The callback model also exposes a separate closed dispatch census for rules
that need actual source arguments. It retains module-qualified callback and
registration identities, bound source frames, each dispatch argument, and
formal-to-actual transport edges. It returns all records or an explicit
incomplete result; source, allocation, and budget failures propagate.
A caller-owned scratch allocator owns the records, and the original source
documents and resolver must outlive them.

This census is not the alignment certificate above. It can describe a null
context or same-object arguments. A consumer must prove its own null,
alignment, lifetime, or storage claim for every record. Escaped or rebound
registrations and unexpanded loop-generated actuals remain incomplete.
An immutable factory-result pointer header proves only alias identity. Its
separate, complete callback/context-use census must still close pointee uses.

A function-valued sibling field needs an exact same-cell carrier argument.
Its resolved source body must preserve the callback/context pair.

The physical cell and the runtime value have separate identities. A fresh
struct cell has distinct inline fields. An older pointer graph cannot borrow
that separation unless its header remains unchanged and the carrier address
never enters that graph. Pointer-header rebinding and opaque mutations refuse
the certificate.
A later callback registration does not create a new physical cell.

A by-value copy creates a new physical cell with source-proved callback and pointer headers.
The proof keeps that header snapshot separate from later reads through the source cell.
Both cells still need a complete header and address-publication census.

Sibling methods need complete target and unrooted effect proofs, or a separate
source proof that confines each effect to storage outside the physical carrier.
A source body alone does not exclude opaque calls, global writes, or memory assembly.
The confined mutex proof requires the selected immutable standard-library IO
vtable and its authenticated futex handlers. It does not assume that arbitrary
IO providers are safe, or change the generic unrooted effect result.

The standard library's resolved `Thread.spawn` declaration supplies its
callback and tuple-copy contract. A project function with the same name does
not. Its source body must establish the transport instead.

Ordinary non-optional typed pointers, including allocated pointers and method
receivers, establish the same pointee alignment. A non-optional slice's `.ptr`
also establishes byte alignment, or its ordinary element alignment when the
destination has the same element type. `@ptrCast` and `@constCast` do not add
alignment. Explicitly underaligned or `allowzero` pointers, unknown calls,
escaping returned aggregates, and unproved persistent registrations remain
findings.

Pointer and optional type aliases are resolved by declaration identity, including
namespace-qualified aliases. The proof also retains the original pointer syntax:
an alias does not erase `align(...)` or `allowzero`. A null rejection discharges
only the unwrap; the canonical source and destination pointees must still match.
An explicitly stronger destination alignment remains a finding.
Canonical pointee identity remains nominal: two distinct structs with identical
fields do not become interchangeable through pointer aliases. Namespace aliases
and `const` pointer qualifiers do not change the underlying pointee declaration.
Selecting an owner's pointer typedef does not publish its callback. Both the
resolved alias and its source declaration must name the exact recovered pointee.
Each actual address still needs the ordinary alignment and non-null proof.

Review of one safe registration does not close a public or escaping callback.
When other registrations or SDK userdata origins remain unresolved, the rule
keeps the finding even if the selected in-tree binding is correctly typed.

## Why it matters

`@alignCast(x.?)` chains two failure modes:

1. **Null panic**: `.?` panics in Debug/Safe if `x` is null. This silently trusts that the pointer is always non-null — a trust that may be violated by the calling convention, a platform-specific code path, or a race condition.

2. **Alignment panic**: `@alignCast` panics in Debug/Safe if the pointer is not aligned to the required alignment. For context pointers passed through `*anyopaque` (a common C callback pattern), the alignment depends on what was originally stored — which may not match the cast target.

Combining both into a single expression means two runtime invariants are being asserted at once, with no error handling for either failure. The correct approach is to type the pointer as non-optional from the start (eliminating the `.?`) and to ensure alignment statically.

## Real-world instance

- **tigerbeetle/tigerbeetle#3717** (`io: even_listen`): `@ptrCast(@alignCast(ctx.?))` was used to recover a typed pointer from a `?*anyopaque` callback context. If `ctx` was null (possible in some code paths), the forced `.?` would panic. Fix: changed all `?*anyopaque` context parameters to `*anyopaque` throughout the codebase, removing the need for `.?` at every dereference site.

## Fix

```zig
// Instead of (panics on null AND on misalignment):
fn dispatchCallback(ctx: ?*anyopaque) void {
    const self: *Handler = @ptrCast(@alignCast(ctx.?));
    self.handle();
}

// Make the context non-optional at the call site:
fn dispatchCallback(ctx: *anyopaque) void {
    const self: *Handler = @ptrCast(@alignCast(ctx));
    self.handle();
}

// Or guard the optional before casting:
fn dispatchCallback(ctx: ?*anyopaque) void {
    const raw = ctx orelse return;
    const self: *Handler = @ptrCast(@alignCast(raw));
    self.handle();
}
```
