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
  The rule checks the whole receiver path and its root binding. A local
  built from `.{}` can remain private when a callee fills it through an
  address argument in a discarded call, including
  `if (condition) try fill(&parent);`. The condition, callee, and arguments
  must not name the other root. The enclosing `if` must itself be a
  statement, not an initializer or another expression that keeps the
  result. Header copies, stored addresses, pointer aliases, and unresolved
  receiver chains remain possible aliases and are reported.
- The callee grows a **different** ArrayList than the one being iterated.
  The rule uses callee growth paths to identify the affected parameters and
  fields. A proved sibling-field growth or a call that cannot reach the
  iterated receiver does not fire. Unknown growth effects stay conservative.
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
