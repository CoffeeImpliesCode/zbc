# heap-use-after-free

Reading heap payload after its corresponding `free` / `destroy`, or
returning a dangling heap address. The allocator owns the released
storage; dereferencing it is invalid.

## Example

Incorrect — `buf` is read after free:

    const buf = try allocator.alloc(u8, 32);
    allocator.free(buf);
    process(buf);                       // ← use after free

Fix — perform all reads before the free, or assign a fresh value
through the same name before re-use:

    const buf = try allocator.alloc(u8, 32);
    process(buf);
    allocator.free(buf);

## When this might be a false positive

- Conditional free + use on disjoint paths.  zbc tracks state per
  basic block and joins conservatively at merges; one branch
  freeing and another using can produce a join state that flags the
  use.  Reshape the code so the free and use are not joined.
- Re-allocation through a path zbc can't classify.  A fresh
  `buf = alloc(...)` clears the prior free, but if the rebind goes
  through an unrecognised builder method, the prior free state may
  persist.  Naming the constructor `init`/`create`/`new`/`open`
  helps the classifier recognise the fresh allocation.
- **A view is not a payload read.** `free(buf); _ = buf[0];` is
  a use-after-free. Building `buf[a..b]` reads the descriptor, not
  its elements. A call that reads those elements and the source
  operand of `@memcpy(ptr, buf[0..])` must still check the backing
  allocation.
- **A pointer or slice header is not its backing allocation.** Reading
  `bytes.len`, copying `bytes.ptr`, or copying the descriptor does not
  read released elements. Copies keep the allocation identity: a later
  index, dereference, payload-reading call, return, or output escape
  must still check that identity. This distinction requires an exact
  source expression and resolved pointer/slice type. An unresolved
  field chain is not proof of a header-only read.
- **The object holding a header must still be alive.** After
  `allocator.destroy(owner)`, `owner.bytes.len` reads the released
  owner's bytes. The slice's header-only classification does not
  excuse this parent-object use-after-free. The same rule applies to
  intermediate pointer fields in a nested chain.
- **Runtime headers must be initialized.** An undefined slice's `.len`
  is an undefined-value read, unlike a fixed array's static extent.
  The SDK's empty-slice `free` no-op still evaluates its argument.
  Its descriptor and every containing pointer owner are read before
  release handling. An empty backing value does not excuse an
  undefined header or a dead object that holds that header.
- **A lifetime origin does not prove a non-null value.** An allocation
  with `catch null` and a nullable borrowed return can both carry
  lifetime evidence without proving that the optional contains a value.
  Null-branch pruning needs a separate value proof for the exact
  selected place. Every returning alternative must support that proof.
  A physical store and its output-custody record share one evaluated
  value. The custody record does not read or invalidate the source again.
  Field facts also require a unique canonical path representation.
  A quoted field such as `@"a.b"` must not supply a fact for the
  distinct nested field `a.b`. Unions, unresolved layouts, and
  ambiguous flat paths do not supply this proof. A current value
  selection can cross a pointer ancestor only through exact typed
  owner selections; mutation revokes that value fact. This does not
  prove field independence or a stable physical output address.
- **Heap output custody is separate from stack-escape policy.**
  A proved scope-bound stack installation can omit a stack warning,
  but it must still record any heap allocation published through
  that output. A conditional defer may retire that custody only
  for the same stable physical output slot. A sibling null check,
  a pointer-ancestor selection, or a rebound root is not that slot.
- **Loop allocation generations remain a precision limit.** Repeated
  execution of one allocation site can merge distinct iterations.
  A loop-carried slice replacement, followed by conditional deferred
  cleanup, can therefore produce an extra lifetime warning. The
  header and output-custody proofs above do not separate those
  allocation instances or prove that a real release can be skipped.


## Borrow-tracking via inference

When the use happens through a borrow rather than the freed pointer
itself, zbc infers the ownership chain from body shape:

- A method whose body calls `allocator.free(self.field)` or
  `allocator.destroy(self)` is inferred as taking ownership of its
  receiver.  Subsequent uses of the receiver (or aliases captured
  before the call) fire as use-after-free.
- Pointer-typed struct fields (`*T`, `?*T`) are treated as borrows;
  reads do not propagate ownership.  Non-pointer fields (`[]u8`,
  `T`) read as owned-by-parent when the destructor frees them.

Example:

    const Owner = struct {
        data: []u8,
        pub fn die(self: *Owner, gpa: std.mem.Allocator) void {
            gpa.free(self.data);
        }
    };

    var owner = Owner{ .data = try gpa.alloc(u8, 16) };
    const borrowed = owner.data;
    owner.die(gpa);
    _ = borrowed[0];             // ← released backing storage is read

## Turning other rules off

This rule answers to its own `--disable` / `--enable` entry and to
nothing else.  A neighbouring rule being off never silences it: with
`use_undefined` disabled, reading a field whose payload was already
freed still fires here, even when the owner holding that field was
never initialised.  That owner's own finding is simply not reported,
and this one takes the site instead.

The two are not in tension — they name different facts about the same
read.  The owner's liveness is about whether the bytes being read
exist at all; this rule is about the allocation the field points at.
When both hold, the owner's is the better report and is the one you
get.

## Related

- `heap-double-free`: freeing the same pointer twice.
- `arena-use-after-kill`: same shape, but the resource is an arena
  rather than a single heap allocation.
