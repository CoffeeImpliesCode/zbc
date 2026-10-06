# tagged-union-payload-early-exit

An assignment of the shape `<path> = .{ .<Tag> = <expr> };` where `<expr>`
contains a `try` causes Zig's compiler to write the union tag to the result
location **before** evaluating the payload expression.  If the payload
expression propagates an error and exits early, the LHS is left with the new
tag but with the **payload bytes from the previous variant** — a corrupt state
that subsequent code (including `errdefer` cleanup handlers) may misinterpret as
a valid value.

The detector keys on `try` inside the single-field literal.  An early-exit
`catch` payload (`catch |err| switch (err) { … => return; }`) is the same
hazard with the same fix, but it is not what this rule matches on.

## Why this matters

Tagged unions in Zig are represented as `{ tag, payload }`.  When the compiler
lowers `x = .{ .NewTag = expr }`, it must:

1. Write the new tag to `x.tag` (flips the active variant).
2. Evaluate `expr`.
3. Write the result to `x.payload`.

If `expr` contains `try` and the attempted operation returns an error, execution
transfers out of the enclosing function **between steps 1 and 3**.  The tag has
been updated but the payload bytes still hold whatever the previous variant
stored — an aliased, potentially dangling interpretation of the data.

Any subsequent read of `x` (for example an `errdefer x.deinit()` registered
before the assignment, or a caller that inspects `x` on the error path) will
mis-dispatch on the new tag and read the old variant's payload bytes as if they
belonged to the new type.

## Example

```zig
// BUG: tag `.err` is written to `resolve.value.tag` BEFORE the `try`
// evaluates.  If `logger.Msg.fromJS` returns `error.JSError` the handler
// returns early — `.err` is the active tag but the payload is whatever
// `.pending` held before, so the caller's cleanup reads those bytes as
// a `Msg`.
resolve.value = .{ .err = try logger.Msg.fromJS(globalObject, value) };

// FIX: hoist the fallible expression before the literal assignment
const msg = try logger.Msg.fromJS(globalObject, value);
resolve.value = .{ .err = msg };
```

## The storage-privacy boundary

A half-retagged union is only a bug when something can still read it after
the tag has flipped.  On the error path a `try` unwinds straight out of the
function, so a **by-value local whose storage never leaves the frame** is
harmless: the frame dies with the corrupt bytes still sealed inside it, and
no handler runs that would interpret them.

Observability is bounded by the frame's own lifetime.  The reader that
matters is one running while the frame is still unwinding — a callee entered
before the `try`, or the frame's own cleanup.  A pointer the frame handed out
and never used again is not a use-after-return; it is simply a pointer the
callee was given while the frame was still alive.

The question is never "was `&root` written down" — `_ = &result;` writes it
down and reaches nobody — but **where it went**.  The rule reports a local's
assignment when the address reaches a destination outside this frame
**before** the `try` runs.  These report:

- the storage belongs to a **parameter** (`resolve.value = .{ .err = try … }`)
  — the caller owns it and inspects it on the error path;
- the local is declared through a **pointer** type, so the write lands in
  storage the frame does not own;
- a `defer` / `errdefer` registered before the assignment **mentions the
  root** — that cleanup runs after the tag flipped;
- the root's **address reaches a destination outside the frame**: handed to a
  callee (`observe(&result)`, including the grouped `observe(&(result))`),
  stored into an owner the frame does not own (`registry.saved = &result`),
  or packed into an aggregate that is itself published (`const holder =
  Holder{ .spec = &result }; observe(&holder);`).

  The address must be a real address expression, so `bits & result.mask`
  — a binary operator, not `&root` — is not publication.

These stay quiet, because nothing that survives the error path ever reaches
the address:

- the address **discarded outright** (`_ = &result;`);
- an alias or aggregate that is bound and then **discarded**
  (`const alias = &result; _ = alias;` with or without a type annotation;
  `const holder = Holder{ .spec = &result }; _ = holder;`);
- publication **after** the assignment (`observe(&result)` following the
  write) — control never reaches it, the `try` leaves the function first;
- the address of an **unrelated local** (`observe(&scratch)`);
- **private heap storage** whose only failing-path cleanup releases the raw
  allocation without reading the element — a `defer gpa.free(fields);` whose
  receiver's declared type resolves to `std.mem.Allocator` hands the bytes
  back and never interprets the corrupt union.  See
  **Who proved the release** below for what "resolves" excludes.

## Writing through a loop capture

`for (fields) |*field| { field.kind = .{ .bit_field = .{ .bit_offset = try … } }; }`
does not retag a local — it retags an **element of `fields`**.  The capture
is only a name for the write; the storage is whatever the loop iterates, so
the privacy question is asked of that storage instead.  ocean's
`decodeModuleLayouts` is the shape this resolves:

```zig
var fields: []Field = &.{};
if (field_count != 0) {
    fields = allocator.alloc(Field, field_count) catch return error.OutOfMemory;
}
errdefer if (fields.len != 0) allocator.free(fields);
for (fields) |*field| {
    field.type_id = try readModuleTypeReference(reader, type_count, type_count);
    // …
    1 => field.kind = .{ .bit_field = .{ .bit_offset = try reader.readU16(), … } },
}
```

The element type comes from the storage itself: the annotation on the
declaration (`var fields: []Field = …`), the type argument of the allocation
that produced it (`allocator.alloc(Field, n)`), or an alias of one of those.

Such a capture stays quiet only when **every** step of the proof holds:

- the iterable is a plain name bound to storage this frame owns — never a
  **parameter**, whose slice the caller owns and reads on the error path;
- its element type resolves, so the write is known to land in a slice rather
  than in something the rule cannot place;
- a `defer` / `errdefer` **dominates** the write: the block it is registered
  in is the write's own block or an **ancestor** of it, and it is registered
  unconditionally;
- that cleanup releases the storage **raw** — a `free` whose receiver's
  declared type resolves to `std.mem.Allocator`.  `deinit` / `destroy` can run
  destructors that read the corrupted element, and a `free` this rule cannot
  resolve is not a release at all;
- no other cleanup registered before the write reaches the storage, or the
  captured element, by any route.  A cleanup that **both** releases raw and
  reads is an observer: the release hands the bytes back, and a read that
  follows it still interprets them;
- the **capture itself** reaches no callee before the write, and the storage
  neither takes its address nor is published — the same escape and
  publication proofs a plain root gets;
- every other mention of that storage before the assignment is its own
  declaration, a reassignment, or a loop header.

These still report, and each is one fact away from the quiet shape above:

- the slice is a **parameter** (`fn update(fields: []Field) !void`);
- the slice reached an owner **before** the write (`sink.* = fields;`);
- the **release is in a sibling block** — `{ errdefer gpa.free(fields); }`
  written in its own block before the loop.  That block is the same DEPTH as
  the write and neither encloses the other, so its scope has ended by the
  time the write runs and nothing it registered is left;
- the release is in a **mutually exclusive arm** —
  `if (flag) { errdefer gpa.free(fields); } else { for (fields) |*field| { … } }`.
  The arms are exclusive, so on no failing path are they both live.  (A
  braceless `if (flag) errdefer …;` is the same mistake and is **not a Zig
  program** — a `defer` is a block item, never a prong body — so every
  conditionally armed cleanup is a braced arm, and the ancestor-block test is
  what refuses it.)
- a **cleanup registered before** the write reads the storage or the captured
  element (`errdefer trace(fields[0].kind);`), or does both in one statement
  (`errdefer { gpa.free(fields); trace(fields[0].kind); }`);
- **nothing releases** the allocation — the release is part of the proof, so
  an unreleased capture is reported rather than assumed private;
- the **capture is handed out** (`observe(field);` inside the loop body) — it
  is a pointer to the element the retag corrupts, so a callee holding it can
  still read the union;
- the iterable is **not a plain name** (`for (self.fields) |*field|`), or the
  span belongs to a `while` / `if` capture rather than a `for` header: the
  storage cannot be placed, and what cannot be placed is not evidence of
  privacy.

## Who proved the release

The quiet half rests on one release, and "a `free`" is not enough to name it.
The rule resolves the **receiver's declared type** — a parameter, a `const`
bound to one, or an alias of either — through the scopes that type is written
in, and requires it to be `std.mem.Allocator`.  A bare `free(fields)` (a
function in the file, not the allocator's method), a `free` method on any
other type, and a receiver the walk cannot place (`x.gpa.free(…)`,
`arena.allocator().free(…)`, an `anytype` parameter) all fail to resolve.

A failure to resolve is a **refusal, and refusals report**.  It is never read
as privacy: the slice the call was handed stays an ordinary read inside that
cleanup, so the cleanup classifies as an observer and the finding stands.
The cost of this is a false positive on code that releases through a thin
wrapper — `errdefer pool.free(fields);` where `pool` is this project's own
allocator — which is reported rather than suppressed.  That is the direction
this rule takes everywhere else (see **Unresolved target types** under
*false positive*), and it is why a user-defined `free` that does **not**
inspect the union is reported just as the one that does.

Registration is a separate fact from release.  `errdefer` arms unconditionally;
the `if` in ocean's `errdefer if (fields.len != 0) allocator.free(fields);`
guards **which** release runs, not whether the errdefer is armed, and when the
guard is false the storage is the empty `&.{}` its declaration gave it, so
there was nothing to release.  What must be proved is that the cleanup's block
encloses the write's — which is what rules out a sibling block and a
mutually exclusive arm, the two shapes a brace DEPTH cannot separate from a
real enclosing block.

## Which binding a use names

One spelling can be two declarations, and the one a use names is the
declaration whose own block still spans the use.  Every lookup in this rule
therefore goes through `LocalBindings.findAt` rather than through "the newest
declaration before this token".

On a well-formed program the two agree, and that is an adjudication worth
recording rather than a silent detail.  Zig diagnoses shadowing
(`zig.AstGen.detectLocalShadowing`; "local variable shadows declaration of
'…'"), and neither the ocean checkout nor this repository contains a single
declaration that shadows a parameter or an enclosing local — while shadowing
*captures* (`if (opt) |opt|`, which is why the AST has a dedicated
`shadowing_capture` node) are idiomatic.  A `var` that shadows a parameter is
therefore not a fixture this rule may be tested with: it is not a program Zig
compiles.  The scope-respecting query is still the one that answers the
question being asked, so the rule uses it rather than relying on the language
to make the two equivalent.

## Shape limits

- The target must be a plain path whose token before `=` is an identifier
  (`resolve`, `self.value`).  `fields[0] = …` and `first.* = …` end in `]` and
  `*`, resolve to no root location, and are not reported by this rule.
- The literal must have exactly one top-level field.
- The target's type must resolve to a `union(enum)`.  A target that resolves
  to an ordinary struct or an untagged union is not reported; a target whose
  type cannot be resolved is treated as a tagged union and reported.

- When the target's root is a loop capture, the type checked is the ELEMENT
  type of the storage the capture iterates.  An element type the rule cannot
  read out of a declaration, an allocation or an alias is treated as
  unresolved, which is the conservative direction: the target is reported
  unless the storage privacy proof above holds.

## When this might be a false positive

- **Unresolved single-field struct literals**: a resolved ordinary struct or
  untagged union is excluded. If the target type is unresolved, a
  single-field struct assignment can be reported as a possible union write.
  Multi-field literals are excluded. Resolve the target type before deciding
  that the tag-change hazard applies.

- **`const`/`var` declarations**: `const x = .{ .tag = try f() };` is not an
  assignment to an existing location — no prior variant exists — so the rule
  skips it.  Only assignments to pre-existing paths (`self.field = …`) are
  checked; see **Shape limits** above for the forms that are not resolved.

- **Unresolved target types**: when the target's type cannot be resolved the
  rule assumes a tagged union and reports.  That is the conservative choice —
  the alternative is silently dropping a real partial-retagging report — so
  treat it as a reason to look, not as proof.

- **Loop captures whose release does not resolve**: the quiet half of the
  capture rule needs a `defer` / `errdefer` that raw-frees the iterated
  storage through a receiver whose declared type is `std.mem.Allocator`, in a
  block that encloses the write, registered unconditionally.  Code that
  allocates and returns the slice, releases it only after the loop, releases
  it through a project wrapper (`errdefer pool.free(fields);`), or arms the
  release in a branch the write cannot reach, is reported even though the
  retag may be unobserved — the release is what the proof is made of, and a
  release this rule cannot resolve is not one.

- **A release in a block that merely shares the write's depth**: the proof
  reads the cleanup's block against the write's block, not a brace count.  A
  sibling block and a `while` body both read as "not enclosing" even though
  both are at depth 1 relative to the write in some readings; the former is a
  true negative for the rule (the scope really has ended) and the latter is
  the quiet half.
