# deinit-order-violates-construction-dep

Within a single fn body, `<A> = <T>.init(&<B>, ...)` creates a
dep edge B→A (A borrows from B).  Later `<B>.deinit(...)` runs
BEFORE `<A>.deinit(...)`.  A's deinit may dereference its
borrowed pointer to B — but B is already torn down → UAF.

Canonical LIFO invariant: deinit in REVERSE construction order.

## Canonical bug (tigerbeetle/tigerbeetle#3732)

```zig
env.grid_verify = try Grid.init(...);
env.manifest_log_verify = try ManifestLog.init(&env.grid_verify, ...);
// ...
env.grid_verify.deinit();           // ← BUG: parent first
env.manifest_log_verify.deinit();   // ← child uses dangling parent
```

## Fix

```zig
env.manifest_log_verify.deinit();   // child first
env.grid_verify.deinit();           // parent last
```

## Deferred cleanup contract

AST statement bounds identify both `defer` and `errdefer` calls,
including conditional statements and deferred blocks. The condition
does not make the call immediate. `errdefer` runs only on an error exit,
but follows the same reverse-registration order when it runs.

Separate registrations in the same scope execute in reverse order.
This sequence is safe when cleanup runs:

```zig
var context = Context.init();
defer if (typed) context.deinit();
var resolver = Resolver.init(&context);
defer if (typed) resolver.deinit();
```

The resolver runs first and can still access the context. Reversing
the registrations is unsafe and must report:

```zig
var context = Context.init();
var resolver = Resolver.init(&context);
defer if (typed) resolver.deinit();
defer if (typed) context.deinit();
```

Calls within one deferred body keep their statement order; the
detector must not reverse them as if each call had its own defer.
Defers in different scopes run at their respective scope exits,
not in one function-wide LIFO stack. Immediate calls execute before
pending defers in that scope.

Nested defers are compared within their enclosing deferred body.
AST bounds, not token adjacency or receiver names, determine
whether cleanup is deferred.

Error-path cleanup obeys the same dependency:

```zig
var context = try Context.init();
errdefer context.deinit();
var resolver = try Resolver.init(&context);
errdefer resolver.deinit();
```

An error after the second registration tears down `resolver` before
`context`. Neither call is treated as an immediate call. The rule still
reports reversed error-cleanup registrations.

## Why the detector is precise

- Dep edges are collected only from explicit `.init(&<B>, ...)`
  shapes — passing by VALUE doesn't create a borrow dep.
- Owner comparisons retain the full receiver path. `left.context` and
  `right.context` are distinct owners even though their final member
  names match. Member declaration order does not establish a dependency.
- Constructor type aliases and qualified import paths do not change
  the dependency: the edge uses the actual `&owner` argument and LHS,
  not the constructor type's name.
- Reports at the dependent's deinit, using cleanup execution order
  rather than source order alone.

## Limitations

- Only catches deinit pairs within a single fn body.
- Doesn't distinguish "init takes &B for read-only" from "init
  stores &B" — the latter is the actual UAF case, but both
  shapes look the same syntactically.
- Missing cleanup is not an order violation: the rule requires both
  matched owner cleanup calls. Separate leak rules handle absent cleanup.
- Conditional cleanup is checked syntactically; the rule does not
  prove that arbitrary conditions can hold on the same path.
