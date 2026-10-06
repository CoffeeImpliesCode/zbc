# heap-use-after-free

Reading or returning a heap pointer after the corresponding `free` /
`destroy` call.  The value's storage has been returned to the
allocator; reading it is undefined behavior.

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
- **A slice argument is not automatically a read, and a copy out of
  one is.**  `free(buf); use(buf[0..1]);` is a genuine
  use-after-free — the slice aliases the freed allocation — and a
  single index is reported for the same reason.  What zbc does NOT
  do is report every `buf[a..b]`: building a slice reads nothing,
  so passing one to a function that only writes through it is
  silent, while `@memcpy(ptr, buf[0..])` on the source side is a
  whole-array read and fires.

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
    const borrowed = owner.data; // borrowed origin tied to owner
    owner.die(gpa);              // inferred as takes ownership(self)
    _ = borrowed;                // ← heap-use-after-free fires

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
