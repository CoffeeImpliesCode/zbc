# slice-loop-reentrant-grow

A `for (<recv>.items)` loop captures the ArrayList's backing slice — its
`ptr` and `len` — at the start of iteration.  If any code inside the loop
body calls a function that **grows the same ArrayList or an alias of it**
(via `append`, `resize`, `ensureCapacity`, etc.), the backing buffer may
be reallocated. After the reallocation the loop's captured `ptr` dangles
into freed memory; subsequent iterations access freed storage.

This is the re-entrant (callee-indirect) variant of the pattern.  Direct
same-function grows are caught by `arraylist-items-slice`.

## Example

Incorrect — `executePendingNapiModule` can append to `m_pendingNapiModules`
while the loop is iterating it:

    for (globalObject.m_pendingNapiModules.items) |mod| {
        executePendingNapiModule(globalObject, mod);
        // ^ may append to m_pendingNapiModules → realloc → items ptr dangles
    }

Fix — snapshot the count before the loop, or collect items into a
temporary list before processing:

    const pending = try arena.dupe(Module, globalObject.m_pendingNapiModules.items);
    globalObject.m_pendingNapiModules.clearRetainingCapacity();
    for (pending) |mod| {
        executePendingNapiModule(globalObject, mod);
    }

## When this might be a false positive

- The grown list is a **different object** than the one being iterated.
  Receiver field names alone do not prove that two lists share storage:
  `parent.allocations` and `output.allocations` can be independent lists.
  The rule resolves receiver binding origins, including immutable aliases
  and copied list headers. Different parameter names do **not** prove
  independence: two pointers can point to the same object. Independent
  storage requires a fresh initializer proved from its declarations and
  a private local before the growth call. Constructor names and `.empty`
  spelling alone are not proof. Rebinding, header replacement, escaped
  addresses, and unresolved receiver chains remain possible aliases.
  A `*const` view does not change this: another mutable pointer or copied
  header can still reallocate its backing buffer. A quiet consumer needs
  an actual private fresh output, not only constness on an incoming tree.
  A header store before the call also prevents a sibling-field exemption.
  An address handover must resolve to a readable helper with scalar stores
  and authenticated SDK list growth. Header stores and opaque calls cannot
  certify that the local remains private.
- The callee grows a **different** ArrayList than the one being iterated.
  The rule uses canonical growth paths to identify affected parameters and
  fields. A fresh output stays separate only when the caller's storage proof
  and the callee's complete growth paths agree. The callee must also preserve
  header identity: scalar stores and authenticated SDK list growth are allowed,
  but header copies and opaque callees are not. Once those certificates are
  complete, a generic write summary adds no storage-identity evidence:
  ordinary SDK growth itself writes the destination header. Unknown
  provenance and incomplete growth effects stay conservative.
- An opaque callback can grow storage through its captured context. The
  neutral closed-dispatch census supplies **all** registrations, leaf
  arguments, source frames, and transport edges. The collection consumer
  separately requires a private fresh iterated list at every dispatch,
  with no earlier publication or transport of that local. The privacy
  horizon is the invocation, not registration: a header copied into the
  captured output after binding still prevents a storage certificate.
  The census distinguishes an inline sibling component from the address
  of its enclosing callback carrier. A component header store or a canonical
  SDK list growth/lifecycle call does not by itself replace sibling callback
  slots. Pointer fields, raw child addresses, and project methods that can
  recover or publish their parent do not gain that exception.
  Same-object arguments, copied headers, NULL contexts, escaped dispatchers,
  and unsupported edges retain the finding. A complete census and an alignment
  proof alone do not establish disjoint backing storage.
- A collection access only **computes the iterable**. For example,
  `for (successors[queue.items[head]])` borrows the successor slice, not
  the queue's backing buffer. Growing a dynamically indexed queue does
  not invalidate that distinct slice. Each nested `for (queue.items)`
  still has its own borrow horizon.
- The ArrayList is **pre-allocated** (via `ensureTotalCapacity`) before the
  loop and the callee only calls `appendAssumeCapacity`-family methods (which
  cannot reallocate).  Those methods are excluded from `may_grow_collections`
  detection by design.

## Related

- `arraylist-items-slice`: same bug when the grow call is in the same
  function body (direct, not via a callee).
- `arraylist-element-ptr`: element pointer `&list.items[i]` invalidated by
  a direct grow call.
- `hashmap-iter-mutation`: the HashMap equivalent.
- `iterator-invalidation-mutation`: general iterator + mutation pattern.
