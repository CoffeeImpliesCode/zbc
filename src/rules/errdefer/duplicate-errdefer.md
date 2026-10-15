# duplicate-errdefer

Two `errdefer` statements register the same cleanup call (e.g.
`errdefer X.deinit();`) against the same receiver `X` in one
function body.  On the error path Zig fires errdefers in reverse
declaration order — and here both registrations fire — so the
cleanup runs twice on the same resource.  The second call hits
its `deinit` assert, double-frees the underlying handle, or
corrupts shared state.

The fix is to remove the duplicate registration.  The typical
cause is copy-paste during refactoring: an `init` step is moved
or duplicated without removing the matching `errdefer`.

## Example

Incorrect — `errdefer command.io.deinit()` is registered twice;
on error, `IoUring.deinit` runs twice and trips
`assert(self.fd >= 0)`:

    command.io = try IO.init(128, 0);
    errdefer command.io.deinit();

    // …other init steps that aren't here originally…

    command.io = try IO.init(128, 0);        // ← copy-paste of the
    errdefer command.io.deinit();            //    same registration

Fix — drop the duplicate `IO.init` + `errdefer`:

    command.io = try IO.init(128, 0);
    errdefer command.io.deinit();

    // …other init steps…

## Identity and limits

Calls are compared in the same lexical cleanup domain. Receiver and argument
identifiers must resolve to the same declarations; equal spellings in separate
branches do not establish identity. Value copies remain distinct bindings.

Deferred expressions read mutable receivers when the scope exits, not when
the `errdefer` is registered. Reassigning `X` between two `errdefer X.deinit()`
registrations does not make those cleanups independent: both read the final
`X`. Keep separate snapshot locals when the resources have separate lifetimes.

Equal numeric arguments do not identify a resource. For example, two successful
budget reservations of the same byte count need two matching releases.
When type resolution proves that all explicit arguments are numeric values,
this rule does not infer a double cleanup from equal call text alone.
Pointer/slice arguments and argument-free receiver cleanups retain the
duplicate check. Unknown argument types do not obtain the numeric exclusion.

Block-form errdefers are not compared by this rule.

## Related

- `missing-errdefer-between-tries`: the inverse — a fn that's
  MISSING an errdefer between two `try`s.  Together the rules
  catch both under- and over-registration of cleanup.
- `dead-errdefer-in-result-fn`: errdefer that never fires at all
  because the enclosing fn returns `Result(T)`, not `!T`.
