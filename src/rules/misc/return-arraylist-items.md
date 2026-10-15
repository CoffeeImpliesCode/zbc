# return-arraylist-items

Returning a local `ArrayList`'s `.items` slice can lose the allocation's capacity.
The slice records the used length, not necessarily the size the allocator must
receive when the caller frees it.

## What the rule checks

The rule checks the 5-token pattern `return identifier . items ;`. Receiver names,
including `self` and `this`, do not establish ownership. A resolved scalar
`items` field is not an allocation and is excluded.

`return list.toOwnedSlice(gpa)` transfers an allocation sized for the returned slice and does not match this pattern.

## Suppressions

The rule stays quiet only when one of these ownership cases is proved:

1. **A resolved scalar field.** A numeric, Boolean, or enum `items` field
   does not name an ArrayList allocation.
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
3. **A retained caller header.** A pointer parameter retains the original
   handle. A local value copied directly from that parameter's dereferenced
   header or one of its fields can borrow the same backing storage when the
   resolved value type is the standard list. The complete initializer path
   identifies the captured header; copying a pointer value is not this proof.
   Neither constness nor the copy itself establishes an independent owner.
   The caller's original header must remain alive and unchanged.
   Calls need a complete canonical read-only effect across the whole interval
   from function entry through the return, including calls before the copy.
   A standard list grown directly through its caller-owned header can keep
   that handle; growing a copied header cannot. Writes, release, address
   escape, alias creation, and unclassified builtins refuse the proof on
   either side of the copy. Another incoming pointer is not assumed disjoint.
   The scoped binding at each use, not a same-named parameter, identifies
   the source. A copy of a frame-local header does not retain an owner.
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
   Following an allocator initializer requires an immutable binding. A
   mutable local or global header is not a certificate for the provider
   that reaches a later call.
   A local arena alone does not prove that the returned bytes outlive the
   call. A closed private helper can use a caller's local arena only when
   the caller constructs the standard arena with its actual `.init`,
   every normal return directly transfers that exact header in its result,
   and no other use resets, releases, rebinds, copies, or exposes it.
   Error-only `errdefer arena.deinit()` is allowed; a normal `defer` is not.
   Every caller must satisfy this proof. One retaining caller cannot
   establish the allocator authority of another caller.
   The same closed-helper proof can use a standard `FixedBufferAllocator`
   constructed directly from a named, immutable allocation. The allocation
   must come from the actual SDK `Allocator.alloc` with a proved external
   allocator contract. Every normal result must retain that exact backing
   slice. Stack buffers, replacement buffers, normal frees, reset, rebind,
   and aliases do not establish this custody. The stack-local fixed-buffer
   header need not escape with its backing allocation.
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

The cache binds its source module when it binds the source resolver. A private
caller's declaration identity is the source document and its module instance,
not the file path alone. Build-authenticated sources and synthetic unscoped
sources use that same binding; a shared physical source in two modules does
not merge their callers or allocator authority.

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
