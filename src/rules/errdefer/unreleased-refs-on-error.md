# unreleased-refs-on-error

A loop or statement acquires a refcounted reference, and a reachable later
`try` can propagate an error while that reference has no rollback. In typed
analysis, the acquisition must have a source-visible counter increment.
The historical names `reference`, `retain`, `addRef`, `addref`, and
`pendingActivityRef` are candidates, not acquisition certificates. The typed
query also checks other method names and void results. A returned handle key
must select the incremented counter instance.

## Why this matters

Refcounted resources don't have a Zig-level destructor that the
compiler can wire up — the rule "you took a ref, you owe a release"
is enforced only by code.  An `errdefer` registered before a fallible
operation is the canonical place for the matching release.  Without
it, every retry of the failing fallible op leaks one ref per loop
iteration; these accumulate silently until the underlying refcount
becomes unrecoverable (OOM on a GPU descriptor pool, Vulkan/D3D
validation crash, ObjC zombie objects).

The bug is *path-specific*: success leaves no trace.  Only the
fallible-error path leaks, so the symptom shows up rarely and far
from the cause — exactly the shape escape-analysis tools should
catch.

## Canonical example (hexops/mach sysgpu/vulkan.zig PipelineLayout.init)

```zig
pub fn init(device: *Device, desc: *const sysgpu.PipelineLayout.Descriptor) !*PipelineLayout {
    var group_layouts = try allocator.alloc(*BindGroupLayout, desc.bind_group_layout_count);
    errdefer allocator.free(group_layouts);              // ← frees slice, not refs

    const set_layouts = try allocator.alloc(vk.DescriptorSetLayout, desc.bind_group_layout_count);
    defer allocator.free(set_layouts);
    for (0..desc.bind_group_layout_count) |i| {
        const layout: *BindGroupLayout = @ptrCast(@alignCast(desc.bind_group_layouts.?[i]));
        layout.manager.reference();                       // ← refcount ↑ (LEAK SITE)
        group_layouts[i] = layout;
        set_layouts[i] = layout.vk_layout;
    }

    const vk_layout = try vkd.createPipelineLayout(...);  // ← fallible: leak path 1
    const layout = try allocator.create(PipelineLayout);  // ← fallible: leak path 2
    ...
}
```

If either of the post-loop `try` calls returns an error, the existing
`errdefer allocator.free(group_layouts)` reclaims the slice's heap
bytes but never releases the N BindGroupLayout references taken in
the loop.  Each such error leaks N refs.

## Fix

Add a release-class errdefer registered immediately after the loop
(or use a running counter the errdefer reads):

```zig
var taken: usize = 0;
errdefer for (group_layouts[0..taken]) |l| l.manager.release();
for (0..desc.bind_group_layout_count) |i| {
    const layout = ...;
    layout.manager.reference();
    group_layouts[i] = layout;
    set_layouts[i] = layout.vk_layout;
    taken += 1;
}
const vk_layout = try ...;
```

The errdefer fires only on the error path; on success the references
remain with the constructed pipeline layout, which takes them over.

## Why the detector is precise

- Both reference rules use `model/reference_ownership.zig`. Its canonical
  query returns **unknown**, **refused**, or a positive **increment** with the
  declaring resolution frame, formal resource, actual argument, and exact
  counter declaration and instance. Unknown and refused are not balance
  certificates. Imported declarations retain their source frames.
  A resource declaration token authenticates the binding at the copy use.
  It is not a live use token inside the parameter's body scope.
- A positive net increment must reach every successful return or fallthrough,
  and each returned retained handle must select that same counter instance.
  A false guard, an alternate borrowed return, an unrelated metric, a
  decrement followed by an increment, and a different resource do not
  establish acquisition.
- A returned borrowed handle does not acquire a reference. Source-proved
  counter/key handoff or a matching declared decrement protocol is required.
  The copy rule additionally matches the destination's actual release
  protocol to that exact counter; a different counter cannot balance it.
  The query reads release declarations in their canonical container frame.
  It does not pass declaration nodes to an expression-reference resolver.
  Assignment operands contribute their actual effects before the net change.
  Unsupported short-circuit paths cannot supply an increment certificate.
- An opaque or otherwise unproved typed acquisition remains **unknown**.
  Withholding a definite leak report is not proof of no ownership, balanced
  references, or retry safety. The token-only mode retains its historical
  candidate scan when no type resolver is available.
- The function must contain a reachable later `try`. A direct terminal return
  after an acquisition prevents a textual try in a sibling branch from
  supplying an error path. Conditional returns do not prove termination.
- A lexical release-class defer/errdefer is the existing caller-side guard.
  This broad syntactic guard does not certify reference balance.
- For a returned reference passed to a later fallible call, canonical
  declaration and argument identity can expose a related error cleanup.
  The cleanup must already be registered before a branch, return, or
  fallible operation can leave the callee.
- A returned handle's key is selected from its actual declared fields and the
  increment's source path. The key does not need the same name as the counter.
  Unrelated increments, such as a next-ticket counter, do not select it.
- Scalar erasure must be source-visible: the receiver is cleared and the
  returned value derives from its saved fields. The query follows the saved
  value into its actual returned field, including a renamed field. Aliases and
  optional captures retain exact declaration identity, not just matching names.
  Exact `if` and `while` success payloads can forward their scrutinee.
  Element, error, and switch payloads cannot use that identity proof.
- A saved counter-index value needs an immutable, address-free local.
  Its initializer must read the original key before any source mutation.
  A later header clear cannot change that copied value.
  This value proof does not equate counter-owner cells or pointer aliases.
- A cleanup must reach the acquisition's exact returned key, counter field,
  and counter owner. Equal field declarations or keys in different owners
  do not identify the same reference. An opaque cleanup does not prove
  consumption. A report states that rollback is unproved, not that the
  opaque callee cannot release the reference.
- A source-readable no-op, unrelated counter, conditional or skipped cleanup,
  or registration after a possible error does not discharge the report.
  A possible return before the decrement also prevents that proof.
  Every later fallible operation needs its own related cleanup.
  A protected later call cannot cover an earlier unprotected `try`.
  An alias does not preserve an old key or field after a write changes it.
  A mutable local can forward a saved key only before any write or escape.
  The current call's address argument is not an earlier escape.
  Inside a cleanup, preceding writes in that cleanup still invalidate aliases.
- A by-reference cleanup reads storage at exit, not at registration.
  The stability check includes ordinary writes after registration and later
  cleanup registrations that can execute first.
  Inside the selected cleanup, only effects before the selected read count.
  Its later header clear does not revoke an immutable saved scalar.
  Slot escapes and unread calls receiving an enclosing owner retain uncertainty.
- A canonical by-value aggregate formal copies the caller's outer header.
  A source-readable call can preserve that header while it changes a pointee.
  The unrooted-effect query must also prove no global or callback mutation.
  This header proof does not certify reference balance or pointee lifetime.
- This callee evidence concludes only **unknown**, never balanced or safe.
  It prevents a definite leak claim; it is not a storage or ownership
  certificate. Source exclusion, semantic errors, and work-limit failures
  propagate instead of becoming safety evidence.

## Limits

The source counter reader tracks ordinary unit `+=` and `-=` on an exact
declared counter field. A positive net change is required on every supported
success path. Wrapping and saturating arithmetic do not prove a positive
change without bounds evidence and remain unproved. Unsupported loops,
indirect mutation, atomic operations, and unexpanded forwarding bodies can
leave acquisition unknown. A pointer cast
does not establish reference ownership. The returned-storage model is not a
reference-balance model, and an empty or incomplete answer cannot certify
that no reference was acquired. The shared query keeps the existing
50,000-work and 64-frame limits. Resource, source, and cancellation failures
propagate; they do not become safety evidence.

The deferred check conservatively scans the ordinary body suffix without a
proved earlier exit. A write after the last fallible operation can therefore
retain a report. It does not supply a rollback certificate.

