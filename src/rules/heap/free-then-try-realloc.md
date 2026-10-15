# free-then-try-realloc

A heap slice or pointer is freed and then immediately reassigned by
a fallible call (`X = try <allocator>.alloc(...)` or similar) with
no intervening sentinel write.  If the fallible call fails, the
function returns the error and `X` is left pointing at the freed
memory — a subsequent `deinit` (which expects `X` to be either
owned-and-valid or empty) frees the dangling pointer again,
double-freeing or reading freed memory.

The fix is to set `X = &.{};` (or `null` / `undefined` for the
appropriate type) between the free and the fallible call so that
the error path leaves `X` in a safe state.

## Example

Incorrect — `statement.columns` is freed then reassigned through a
`try`; on OOM, `deinit` later double-frees it:

    bun.default_allocator.free(statement.columns);
    statement.columns = try bun.default_allocator.alloc(
        ColumnDefinition41, header.field_count,
    );

Fix:

    bun.default_allocator.free(statement.columns);
    statement.columns = &.{};   // clear before the fallible alloc
    statement.columns = try bun.default_allocator.alloc(
        ColumnDefinition41, header.field_count,
    );

## Cleanup domains

`defer` and `errdefer` register actions; they do not free the value inline.
A single registration before a fallible reassignment is valid when its
initial owner is defined: failure leaves the old allocation available to
cleanup. The rule does not suppress invalid registrations:

- An undefined field registered before its first allocation remains invalid
  if that allocation fails.
- Two active registrations for the same rebound slot can release the new
  allocation twice. Both actions read the slot's current value at exit,
  including an error returned after the second registration; neither action
  captures the old allocation at registration. Nested lexical cleanup
  scopes are distinct domains.
- A real inline release before `try` remains invalid if registered cleanup
  can release the dangling old value on failure.

An error-only reset can protect an inline release when it applies to the
same slot and runs before any cleanup that reads that slot. Reverse
registration order matters. An unrelated or later-running reset does not
provide that guarantee.

Standard allocator operations use authenticated SDK declarations. Member
calls are looked up by the AST field-access token (`.`), not their method
name. A project method named `free` is harmless only when its complete source
summary proves the whole call read-only. Unresolved types or effects do not
count as safe or suppress the existing syntactic release check. Source,
allocation and analysis-budget errors propagate.

## When this might be a false positive

- The enclosing function's caller guarantees `deinit` won't be
  called on the half-initialized struct (uncommon — the safety
  contract is hard to enforce locally).  Adding the `X = &.{};`
  line is essentially free and removes the diagnostic.
- The fallible call is wrapped by `try` but the alloc itself
  cannot fail (e.g. `try alwaysSucceeds()`).  Rare; if you know
  the call is infallible, drop the `try`.

## Related

- `heap-double-free`: the downstream symptom — `deinit` re-frees
  the dangling pointer.
- `heap-use-after-free`: the other downstream symptom — any read
  of `X` after the failed realloc dereferences freed memory.
