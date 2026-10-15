# ref-counted-copy-without-dupe

A struct literal copies an owning field from another struct
(`.field = recv.field`) without acquiring another reference. The
destination's declaration must establish the cleanup obligation; a field
name or an unrelated lifecycle call is not ownership evidence.

When both the source and the copy eventually call a destructor
(`deinit()` / `deref()` / `release()`), the shared underlying allocation
is decremented twice — the second decrement hits a zero-or-negative
refcount, causing a SIGFPE on refcount-assert builds or a use-after-free.

## Example

```zig
// BUG: `source.name` is an OwnedStringCell (refcounted).
// Copying it without calling clone()/dupeRef() means both `source`
// and `copy` share the same allocation.  When both are cleaned up,
// the refcount is decremented twice → SIGFPE.
const copy = Blob{
    .name = source.name,   // raw bitwise copy — BUG
    .size = source.size,
};

// FIX: acquire an extra reference so each side owns one decrement.
const copy = Blob{
    .name = source.name.clone(),   // +1 ref, balanced by copy's deinit
    .size = source.size,
};
```

The canonical instance of this bug is oven-sh/bun#30955, where
`Blob.name` (an `OwnedStringCell`) was bitwise-copied in a
`dupeWithContentType` path; when both the original and the copy were
freed, the second `name.deinit()` hit a `std.debug.assert(rc > 0)`
assertion → SIGFPE.

## What the copy is checked against

The verdict belongs to the declaration the literal **constructs** —
its type expression, the declared type of the field, and whether *that*
declaration runs a reference protocol on *that* field. Ownership is a
property of one type, not of a field's spelling.

| The destination declaration… | Verdict |
| --- | --- |
| runs an acquire/release on the field — `self.f.release(…)`, `self.f.?.release(…)`, or through a value it binds from the field (`if (self.f) \|snap\| snap.release(…)`) | **reported** — the copy is a second owner of one reference |
| takes the field as a pointer (`*T`, `?*T`, `*const T`, `?*const T`) and runs no protocol on it at all | **quiet** — a borrowed view, so nothing is duplicated |
| cannot be bound, does not declare the field, or supplies no readable ownership evidence | **unknown, silent** — no second cleanup obligation is proved |

So a `Plan` that really releases its `data` does not lend that verdict
to a `View` in the same file that merely borrows the same pointer, and a
pointer field is not suppressed by its spelling alone — only by the
absence of any teardown that would ever decrement what it points at.

## Whole-value copies of an owning handle

The struct-literal shape is only one way to duplicate a reference.  A
by-value parameter of an owning type can be copied outright:

```zig
const Shared = struct {
    ref: *Snapshot,
    pub fn deref(self: *Shared, gpa: std.mem.Allocator) void {
        self.ref.deref(gpa);
    }
};

pub fn copy(source: Shared, gpa: std.mem.Allocator) Shared {
    defer @constCast(&source).deref(gpa);
    // BUG: explicit cleanup releases the returned handle's reference.
    return source;
}
```

This pass runs before the field-copy pass because its
evidence is the SOURCE DECLARATION and never a field's name: the
type is an owning handle when one of its own methods **with a
receiver** runs a reference protocol on a field it declares.  That is
the same receiver requirement the cleanup rules read, so a static
`fn free(ctx: *anyopaque, bytes: []u8)` allocator callback is nobody's
destructor, and a `Lease` that only writes through a pointer it
borrows hands nothing back.

Sources are by-value parameters only — an address (`*T`, `[]T`,
`[N]T`) duplicates no count — and never locals: a value the frame
itself built has one owner, and returning one is a move.  A ref-acquire
that reaches the field *before* the copy keeps the verdict quiet,
because that is the fix.

Zig has no automatic destructors. A bare `return source;` without another
use of the source transfers ownership and is quiet. A local binding can
also transfer ownership: `var usage = source; errdefer usage.deinit();`
followed by a single handoff cleans up if the operation fails. A resolved
callee that stores the handle in an owning receiver field proves a
handoff. If a later fallible operation can run the source's error
cleanup, the two owners overlap. A conditional reset or a reset after
that operation cannot prevent the overlap. A proved fresh reset before
it can: its constructor accepts only the standard allocator capability
and returns a literal built from that capability and other proved
constructors. An unread reset or a nonfresh default is not, by itself,
proof that the old allocation has two owners.

Repeated cleanup or unconditional cleanup together with a proved owning
handoff stays reported. A mutable pointer argument is a loan, not another
owning parameter. Unresolved methods, extra header aliases, and unknown
mutation effects do not establish another destructor obligation. They
remain unknown and silent, without certifying a single-owner transfer.
A read-only callee whose positive returned-storage evidence carries the
same owning handle does establish a second owner; a source-proved
disarming method does not leave its old cleanup obligation live.
The proof does not depend on type names or file paths.
A helper's complete storage outcomes can also prove that it releases the
copied handle's entry payload. A second local cleanup then overlaps,
even when the helper is named `append`. A release of a different argument
does not count. Calls and local uses are matched to their exact lexical
bindings; cleanup in a later sibling scope cannot clean an earlier
same-named local.

For a local slice-header copy, the copy's actual uses must prove cleanup or
owning publication before the source's cleanup/publication can prove overlap.

The acquire has to be one the copy cannot be reached *without*: it runs
on every path that makes the copy.  An acquire written inside a branch
that ends before the copy adds a reference on the paths that took that
branch and none on the rest, so it balances nothing —

```zig
// BUG: on the paths where `keep` is false, nothing was acquired and the
// returned handle is a second owner of the one reference `ref` holds.
pub fn copy(source: Shared, keep: bool, gpa: std.mem.Allocator) Shared {
    defer @constCast(&source).deref(gpa);
    if (keep) source.ref.retain();
    return source;
}
```

— while an acquire written in the same branch as the copy is the fix for
that copy, because every path that makes the copy has run it first:

```zig
// QUIET: each arm's copy is reached only through that arm's acquire, and
// neither arm's acquire answers for the other.
pub fn copy(source: Shared, keep: bool, gpa: std.mem.Allocator) Shared {
    defer @constCast(&source).deref(gpa);
    if (keep) {
        source.ref.retain();
        return source;
    } else {
        source.ref.retain();
        return source;
    }
}
```

The branches that decide this are an `if` and its `else`, a `while` /
`for` (which may run zero times), one `switch` prong, and a `catch` /
`orelse` payload.  A plain `{ … }` block is not one: a block that has
been written and left has run.  A `defer`red acquire balances nothing
either, since it runs when the scope exits rather than before the copy.

## When this might be a false positive

- **Plain value copy of a non-refcounted type**: a field named `data`
  or `buf` might simply hold a plain slice or integer — not a
  refcounted object.  If neither side calls a destructor on the field,
  the bitwise copy is safe.

- **An unrecognized ownership transfer**: an incomplete alias or helper
  proof stays unknown. It cannot establish safety, and it cannot by itself
  establish duplicate ownership.

To suppress on a specific line:

```zig
.name = source.name,  // zbc-disable-line:ref-counted-copy-without-dupe
```

## Missed bugs

A pointer destination can look borrowed when its teardown is outside the
readable declaration. If an external helper releases that field, a raw copy
can create two owners without a report. This is a false negative, not a false
positive. The destination's protocol must be visible to this analysis.