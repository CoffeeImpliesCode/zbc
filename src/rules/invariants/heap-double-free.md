# heap-double-free

Calling `free` or `destroy` on the same heap pointer more than once.
The second free either corrupts the allocator's bookkeeping or
aborts immediately, depending on the allocator implementation.

## Example

Incorrect — `buf` is freed on the error path by `errdefer` AND on
the success path explicitly:

    const buf = try allocator.alloc(u8, 32);
    errdefer allocator.free(buf);
    try process(buf);
    allocator.free(buf);                // errdefer also fires on
                                        // a later panic / try error

The errdefer fires whenever the enclosing function returns an
error — including errors thrown by code AFTER the explicit free —
producing a double-free if `buf` was already freed.

Fix — pick one ownership model.  Either let the errdefer be the
sole free for error paths and free explicitly on success, or
disarm the errdefer with a sentinel before freeing:

    const buf = try allocator.alloc(u8, 32);
    errdefer allocator.free(buf);
    try process(buf);
    allocator.free(buf);
    // ↑ safe here because no `try` follows; if there were a `try`
    // after this point, the errdefer would still be armed.

## When this might be a false positive

- Allocator-style methods (`obj.destroy(allocator)` where `destroy`
  is the struct method and `allocator` is the arg) used to be
  misclassified as `allocator.destroy(obj)`.  Fixed in commit
  `1286388`; if you see one, file an issue with the call shape.
- Cleanup can replace a released field with an empty descriptor.
  A later cleanup must select the replacement, not the old entry
  allocation. This also applies when an error callback clears a field
  before a fallible call and a defer releases the saved entry value.
  Preserve the branch and allocation version: two releases of the
  same saved entry are still a double-free. A conditional cleanup is
  not unconditional merely because it appears in an `errdefer`.
- A proved static-empty replacement has no heap allocation to release.
  Replay must retain this fact for that exact generation. It must not
  create a fallback heap identity for repeated frees of the empty value.
  This does not excuse releases of an unknown entry, a real heap
  replacement, or an old heap alias saved before the replacement.
  The no-op also requires the exact SDK `Allocator.free` declaration
  and a nonsentinel slice. A project deallocator or `destroy` does not
  gain this authority from its name. An empty value does not prove a
  non-null pointer or live backing storage. A zero-length free must not
  kill an allocation that the descriptor can still name.
  An explicit `.ptr` or `.len` mutation revokes the old whole-slice
  empty fact. Compiler-generated component copies of one evaluated
  whole value are not separate source mutations.
- Distinct inline fields can retain independent empty facts only
  when their complete canonical layout proves disjoint, uniquely
  represented paths. A union, pointer ancestor, quoted separator,
  cast, or unknown layout does not prove field independence.
- A real release can invoke an allocator callback. Capture its
  released allocation before invalidating mutable header facts.
  Only source-proved private, unexposed inline fields can survive
  that invalidation. A proved SDK empty no-op invokes no release
  callback, but it still reads the argument and its containing owners.
  A project's wrapper can have other effects after that no-op;
  an opaque tail must not inherit the SDK operation's effect guard.
- An incomplete callee trace can retain an authenticated entry-release
  no-op only if every selected exit releases that exact entry version
  through the SDK empty-slice protocol. A different release, unknown
  generation, or replacement allocation cannot inherit the authority.
- Loop-carried replacements can still merge different executions of
  one allocation site. This generation-precision limit can add a
  duplicate-release report. It is not permission to suppress a
  demonstrated repeated free or to change a true safety assertion.


## Related

- `heap-use-after-free`: reading the pointer after the (first) free.
