# double-optional-ptr

`?*?T` — a doubly-optional pointer. Almost always a copy-paste error: the
author wrote one `?` and meant either a nullable pointer or a pointer to an
optional, not both.

## Why it fires

The shape has two independent reasons to be null, and every dereference has
to answer both. A call site that unwraps once still holds a value the type
says may be null, so a second unwrap is required — and a single `orelse`
that handled the "absent" case silently leaves the "absent pointer" case
live. That is a null dereference waiting at the next use.

## The intended spellings

- For a nullable out-parameter — "this call may not write a value" — use
  `?*T`.
- For a non-null pointer to an optional — "the container is here, the value
  may be absent" — use `*?T`.

If the callee truly needs both dimensions of absence, model it as a struct
with a named field per dimension rather than nesting the optionals.

## Detection (Tier 1, flat token walk)

Pattern: `question_mark asterisk question_mark <identifier>` — a parameter
type expression whose tokens are `?`, `*`, `?`, then the pointee type. Fire
at the parameter's type expression, not at the call site.
