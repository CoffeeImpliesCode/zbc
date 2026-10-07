# use-undefined

Reading a value that was declared `undefined` and never assigned
a real value before the read.  In debug builds this is a panic;
in release builds it is whatever garbage happened to be in memory.

## Example

Incorrect:

    var x: T = undefined;
    process(x);                         // ← reads undefined memory

Fix — assign before use, or move the declaration to the point of
first assignment:

    var x: T = undefined;
    initialize(&x);
    process(x);

## When this might be a false positive

- **Pointer initialization requires source proof.** Taking an address
  or calling a method with a mutable pointer does not prove a write.
  zbc credits only the pointee or exact inline field paths that the
  resolved source callee definitely writes before successful return.
  Unwritten fields remain undefined. A boolean success result keeps its
  store certificate on the corresponding result path; ignoring that
  result does not initialize the failure path. Unknown externs add no
  credit. Function and parameter names do not establish initialization.
  A partial field store does not initialize its containing aggregate.
  Only the written field paths can be read until a complete store is proved.

  A direct pointer copy keeps the formal's identity. Reassignment or
  escape ends that proof. A namespace type does not prove its member
  values. Those values require defined initializers.
- **Explicit aggregate values retain their element coverage.**
  Array literals, `@splat`, member arithmetic and indexed inputs are
  checked against the storage they read. Selected value branches retain
  separate element masks. An undefined member or source element remains
  a hole after copying it. Sentinel slices are descriptors, not fixed
  arrays.
- **Complete array payloads survive value copies.** Full element coverage
  over a known array extent permits runtime-index reads. Undefined holes
  remain errors. Immutable constant tables require a resolved declaration
  and a fully initialized literal payload, including nested elements.
  Every table selector must also fit its selected array extent.
  Constant indices and bounded unsigned modulo indices can prove this.
  An unsupported bound adds no destination initialization credit.
  A vector copy or `@bitCast` requires complete source payload coverage.
  A cast does not map partial element coverage across different layouts.
  Declarations and assignments keep cast lifetime origins, but do not
  copy their source slot masks. A valid whole-payload certificate can
  initialize the destination after those earlier transfer steps.
  Sentinel arrays have extra storage outside their logical extent.
  Their logical coverage does not certify all bytes for `@bitCast`.
  A returned array requires a body-definedness proof and covered inputs.
  Pointer types, integer addresses and opaque extern returns prove no
  payload initialization.
- **Optional slice bindings retain their selected descriptor.**
  `const view = optional_slice orelse return` retains the source pointer
  and length on the non-null path, including fresh bindings in loops.
  A local backing array still requires element coverage. Optional slice
  type information does not initialize its backing storage.
- **Defined element writes preserve prior array coverage.**
  A defined runtime-index overwrite preserves existing coverage; it
  does not initialize other slots. Undefined writes retain exact holes
  when their index is known and revoke coverage when it is not known.
  This applies to fixed arrays stored in aggregate fields as well.
  A resolved `std.mem.swap` between two elements of the same complete
  array also preserves coverage. An arbitrary mutable-pointer call
  does not receive this guarantee.
  Source-proven element helpers and optional insertion helpers can
  preserve complete arrays when their actual inputs are defined.
  Preservation adds no initialization credit to incomplete storage.
  Fixed-array pointer captures retain their owner for defined stores
  and for invalidation through opaque mutable aliases.
- **Read-only calls preserve coverage.** A resolved
  `std.mem.doNotOptimizeAway` does not write its input storage. Local
  functions with the same name and unresolved mutable-pointer calls do
  not receive this guarantee.
- **A loop must prove the region it writes.** The generic CFG permits
  zero iterations. Exhaustive proofs require a covering enumeration
  and an unconditional defined store. A bounded `0..array.len` fill can
  establish complete coverage. A runtime `0..count` fill establishes
  only its initialized prefix; reads beyond that prefix remain errors.
  Conditional stores, nonzero starts and interrupted loops do not
  establish these certificates.
  A canonical zero-seeded counter loop can fill a fixed array on its
  normal exit. A fallible store gives no completion credit on an error
  exit. A decrement-before-store countdown gives only its initialized
  prefix, not the unused suffix. Each proof checks current input
  definedness before it adds coverage.
- **Runtime fills certify only their destination region.**
  `@memset(array[0..count], value)` can initialize `[0,count)` when the
  count and value are defined. A nonzero start does not initialize the
  missing leading slots. Enum-based fills require declaration-derived
  lengths and complete index coverage, not an enum name.

Bit-reversal indexes and permutation scatters need additional relational
proofs. A bounded index or an equal iteration count does not establish
the required prefix or scatter coverage.

### Tiled fill — several writes per iteration

    var out: [2 * digest.len]u8 = undefined;
    for (digest, 0..) |byte, i| {
        out[i * 2]     = hex(byte >> 4);
        out[i * 2 + 1] = hex(byte & 0x0f);
    }
    return out;

Read each subscript as an affine function of the loop counter,
`k * i + m`.  The proof fires when every write shares one
multiplier `k`, their offsets are exactly `0 … k-1` (each residue
once), and `k` times the trip count **equals** the target's declared
length.  No `2` and no `+1` is special-cased.  The trip count may
come from a file-level `const`, an array literal, or a fixed-size
array PARAMETER — a `for` over fixed-size storage always walks all of
it, so no `inline` is required.

Refused: a tiling that overshoots the target (the loop would store
out of bounds), a repeated residue (a hole in the tiling), a store
behind a conditional, an unlabeled `break`/`continue`, a `slice`
source (its length is data), an undefined right-hand side, or a
second mention of the target.

### Pointer-capture fill — enumerating the target itself

    var out: [16]u8 = undefined;
    for (&out, 0..) |*byte, i| { byte.* = …; }
    return out;

The enumeration IS the target, so the trip count is the target's
own length and the by-pointer capture names the one element this
iteration owns.  Refused for a different array, a by-value payload,
a conditional store, or an unlabeled `break`/`continue`.  A body
that writes `target[i] = …` with a by-pointer payload is a
*different* shape — the write index is then not proven in range —
and is still reported.

### Manual counter over nested loops

    const input_count = formats.len * workloads.len;
    var inputs: [input_count]Input = undefined;
    var input_index: usize = 0;
    for (formats) |format| {
        for (workloads) |workload| {
            inputs[input_index] = .{ … };
            input_index += 1;
        }
    }
    return inputs;

The counter is what lets a loop whose enumeration says nothing
about the target's layout write a FLAT target.  The product of the
two trip counts must equal the target's declared length, with both
trip counts and the product resolved from declarations — the
`const` that states the length is evaluated as an expression, never
matched by name.  Refused when the counter is seeded at anything but
`0`, when a store sits behind a conditional, when either loop's
source is mutable, when an unlabeled `break`/`continue` escapes, or
when the right-hand side is `undefined`.

### Counter-guarded fill — a runtime `while` plus a counting check

    var fields: [N]E = undefined;
    var count: usize = 0;
    while (it.next()) |field| {
        if (count == N) return false;
        fields[count] = field;
        count += 1;
    }
    if (count != N) return false;
    use(fields);

The counter starts at zero and advances once per iteration, so its
value IS the number of elements written; the check after the loop
means the only way past it is `count == N`.  Together those make
every element written.  Refused without the in-body guard (the
counter could run past the array), without a second advance, when
the check is not the loop's IMMEDIATE next sibling, when its other
arm falls through instead of returning, when the counter is seeded
at one, or when the values stored are themselves `undefined`.

### What counts as a read

A read is anything the program actually evaluates, and only that.
zbc reads `local[i]` as the contents of the element it names, so
`var out: [4]u8 = undefined; if (out[1] == 0)` reports.  A bare
`local[a..b]` reads nothing by itself — building a slice over the
storage is not a read of it. `&local` and `&local[i]` are address
uses, not initialization. A call such as `f(&local)` clears `.undef`
only when the resolved callee proves the required writes.

A whole array counts as read when something copies out of it:
`@memcpy(ptr[0..out.len], out[0..])` moves every element, the ones
no store wrote included, so a partially filled array is reported at
the copy rather than at the return.  The DESTINATION is not a
read: `@memcpy(out[0..], src)` still writes into an undefined
array without firing.

A `const` is storage too.  A file-scope

    const table: [29]i64 = undefined;

is real memory the program indexes into and nothing can ever write
it — the binding is immutable — so `table[i]` reports for the whole
program, not only until some function runs.

### Defined under a guard, read under the same guard re-tested

    var saved_frame: Frame = undefined;
    if (saved_top < stack.len) { saved_frame = stack[saved_top]; }
    …
    if (saved_top < stack.len) { use(saved_frame); }

The read is guarded by the same condition as the write, so the path
that skipped the write cannot reach it.  zbc pairs the two `if`s
only when the conditions are the SAME expression — identical
spelling, nothing declared in between shadowing a name they read, no
call, `try` or subscript in the condition, and nothing able to
change what an operand reads in between.

An intervening assignment to an operand **breaks the pairing**,
with one exception that is the whole idiom this exists for: a
SAVE-RESTORE.  `const saved = stack;` before the first test, then
`stack = saved;`, puts the value back exactly as the save found it,
so everything a call did in between is undone — and the pairing
holds across the call.

The same pairing can cover a returning `catch` handler immediately
after the establishing test. Its straight-line prefix must restore
the saved operands before the matching test. A conditional restore,
a changed guard, or a handler that falls through does not qualify.

Refused, and still reported: a read outside the re-tested guard; a
call that can reach through an operand with no restore after it,
including a call inside the establishing arm after its test; a
shadowing declaration between the two tests; a `defer`/`errdefer` in
between (its body runs at scope exit, which nothing here orders).

- **A read inside the arm of a conditional value that never runs.**
  `return if (live) 0 else scratch[0];` evaluates one arm, not the
  whole conditional.  Each arm is lowered as its own return under
  the assumption its condition makes, so a read that only the dead
  arm has never enters a state where it happens.  A read on the arm
  that DOES run is reported normally — `live` being false there is
  exactly what makes it reachable.

## Related

- (none — this rule is distinct from the resource-tracking rules.)