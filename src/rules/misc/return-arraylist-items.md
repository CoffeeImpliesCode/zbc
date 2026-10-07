# return-arraylist-items

Returning a local `ArrayList`'s `.items` slice can lose the allocation's capacity.
The slice records the used length, not necessarily the size the allocator must
receive when the caller frees it.

## What the rule checks

The rule fires on the 5-token pattern `return identifier . items ;`. It suppresses `self` and `this` receivers because those access a struct field, not a local `ArrayList`.

`return list.toOwnedSlice(gpa)` transfers an allocation sized for the returned slice and does not match this pattern.

## Suppressions

The rule stays quiet in five cases, and each one has to be proved rather
than assumed:

1. **`self` / `this` receivers** — those read a struct field, not a local
   list.
2. **A full-capacity comparison** — `assert(list.items.len == list.capacity)`
   in the same function can prove that the returned slice covers the whole
   allocation. A mention of `.capacity`, a log statement, or a comparison
   against another value does not establish this proof.
   The proof applies at the comparison. Any receiver reference between
   its last operand and the `return` keyword refuses the proof. This
   includes growth, release, rebinding, writes through `.items`, and passing
   `.items` to a callee. The returned slice appears after the keyword,
   outside this interval.
   A `const` or `var` initializer before the comparison that mentions the
   receiver also refuses the proof. It can retain a header or backing-storage
   alias, such as `&list`, `list.items`, or `list`. The rule does not assume
   that such an alias is harmless.
   Growth of another list does not invalidate this proof when no alias
   names the returned list.
3. **A pointer-typed parameter** — `out: *std.ArrayList(u8)` is the caller's
   own list; the caller still holds the handle.
4. **A header copied out of a memo table** — `if (self.memo.get(key)) |cached|
   return cached.items;` hands back a second name for a header the container
   still owns, so nothing is lost when the copy dies at the `return`.
   Growing that copy, freeing it, handing it to a callee, or writing to the
   container between the lookup and the return each refuse the case.
   A callee that can reach this container's storage must have a
   declaration-bound, complete read-only effect for that argument. A write,
   release, or unknown effect refuses the borrow. The callee's name is not
   evidence. Different field names do not prove independent storage.
   A different container can be changed only when its reachable storage,
   including every stored list buffer, is proved fresh and unpublished.
   The callee's unrooted effects are checked even for a call with no
   arguments. Fresh arguments cannot hide a global release or an unresolved
   callback that can change the captured storage.
5. **An arena-backed standard list.** The returned bytes must outlive the
   call, which holds when the local is declared with the standard library's
   list type (`std.ArrayList(T)`, `std.ArrayListUnmanaged(T)`,
   `std.ArrayListAligned(T, alignment)`,
   `std.ArrayListAlignedUnmanaged(T, alignment)`,
   `std.array_list.Aligned(T, alignment)`, or an alias of one)
   **and** every allocator that can reach that buffer is proven to come from
   an `ArenaAllocator` the receiver owns.
   Each of those names is compared against the namespace it was reached
   through, so a spelling that names nothing is not a list: `Aligned` is
   declared inside `std/array_list.zig`, not at the top level, so
   `std.Aligned` names no declaration. A `const` alias is followed wherever
   it is written — file scope or the body that uses it — while a `std` that a
   local declaration, a parameter or a `var` rebinds stops the walk, because
   that name is not the import.
   The alignment argument is a `std.mem.Alignment`, not an integer.
   `std.array_list.Managed(T)` is not discharged by this proof: its
   allocator lives in the list header rather than in each growth call.
   A bare allocator receiver is resolved at its use token, through the
   function's lexical local bindings before any file-scope declaration.
   A local arena does not prove that the returned bytes outlive the call,
   so that case stays diagnosed.
   An explicit borrowed `*std.heap.ArenaAllocator` field also identifies
   the caller-owned arena. Query snapshots can use that typed owner without
   copying; resetting or releasing it before return still refuses the borrow.
   The resolved type proves identity, not lifetime: uses of that arena path
   must only obtain its allocator. A copied arena pointer, a reset or rebind,
   or a bare capture of its owner refuses the proof even in an owner's method.
   A whole-receiver aggregate assignment before the first allocator use is
   allowed only when it creates that standard arena value with `.init`.
   It must not copy an arena header or set an arena pointer. This constructs
   the owner before the borrow exists; the same assignment after allocator
   use refuses the proof. Other pointer captures and aliases are still checked.
   The proof charges:

   - the allocator-taking entry points — `append`, `appendSlice`,
     `appendUnalignedSlice`, `appendNTimes`, `insert`, `insertSlice`,
     `addManyAt`, `replaceRange`, `print`, `resize`, `ensureTotalCapacity`,
     `ensureTotalCapacityPrecise`, `ensureUnusedCapacity`, `addOne`,
     `addManyAsArray`, `addManyAsSlice` — the whole `Aligned` surface that
     takes an allocator as its first written argument, not a hand-picked
     few, so a caller-supplied allocator cannot reallocate what an arena
     grew. The `*AssumeCapacity` and `*Bounded` forms take no allocator and
     cannot reallocate, and `clone` / `toManaged` take one without moving
     this list's buffer; charging any of them would read its first written
     argument — an item, or the new list's own allocator — as the owner of
     the buffer already allocated;
   - the constructor `initCapacity`, on the declaration it initialises and
     on a later `out = …` rebinding;
   - a local declared without a type annotation, whose initializer names the
     type instead.

   The proof is refused outright — the rule fires — when the declaration is
   not the standard list (a project type with an `append` method, a
   file-local type that reuses the name), when the address of the list
   escapes (`rebind(&out, heap)` can rebind the header to anything), when a
   rebinding right-hand side is neither a literal nor a proved constructor,
   when the constructor binds a buffer someone else owns (`initBuffer`,
   `fromOwnedSlice`), or when the buffer is released (`deinit`,
   `clearAndFree`, `shrinkAndFree`, `toOwnedSlice`, …) — a returned slice
   into released memory is a bug whatever allocated it. An unproved case is
   never read as a proved one.

Arena and container proofs share one 50,000-step allowance with their
canonical effect and storage-alias queries for the whole rule check. Their
node scans charge work before scope and path filters. A new return site or
nested query does not reset the allowance. Exhaustion reports the budget
failure at its work site; it never proves a suppression.

## Why it matters

`std.ArrayList(T).initCapacity(gpa, n)` allocates capacity for `n` elements.
The used slice can be shorter than that allocation. Freeing only `.items`
can cause an allocation-size mismatch or fail to release the full allocation,
depending on the allocator.

`list.toOwnedSlice(gpa)` transfers ownership with a length that matches the
returned allocation. Arena-backed storage and a proved full-capacity slice
have the separate lifetime contracts listed above.

## Real-world instance

- **oven-sh/bun#23885** (`toUTF8AllocWithType`): a local byte list returned `.items` without transferring its capacity. The caller freed the used slice rather than the full allocation. On Zig 0.16, use `return list.toOwnedSlice(gpa)`.

## Fix

```zig
// Instead of:
return list.items;

// Transfer ownership:
return list.toOwnedSlice(gpa);

// Or if you want a sentinel-terminated slice:
return list.toOwnedSliceSentinel(gpa, 0);
```
