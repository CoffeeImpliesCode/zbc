# use-undefined

This rule reports reads of proved-undefined bytes, including bytes that can
still hold a proved-undefined value on a reachable path.
UNKNOWN values alone do not cause a diagnostic.
Diagnostic facts and strict defined-value certificates are separate.

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

- **Definite pointer writes initialize only their destination paths.**
  An address or implicit mutable receiver does not read the aggregate payload.
  A resolved definite write removes prior holes from the paths it writes,
  even when the stored value has no positive defined-value certificate.
  A proved-undefined stored value creates holes in those paths instead.
  Unwritten fields retain their holes.
  Strict source and payload certificates still require defined inputs and definite writes.
  A boolean result selects its store certificate only on the corresponding path.
  Ignoring that result does not initialize the failure path.
  Opaque or unresolved calls establish no definite write.
  Names do not establish initialization.
  A partial field store does not certify its containing aggregate.

  A direct pointer copy keeps the formal's identity.
  Reassignment or escape ends that identity proof.
  A defined pointer or slice header does not prove a defined pointee.
  Pointer-parameter pointees are UNKNOWN unless independent facts establish holes or defined storage.
  Reading the pointer or slice header does not read its payload.
  A namespace type does not prove its member values.
  Positive certificates for those values require defined initializers.
- **Explicit aggregate values retain their element coverage.**
  Array literals, `@splat`, member arithmetic, and indexed inputs retain
  facts about the storage they read.
  Arithmetic and selected reads report proved-undefined inputs.
  Selected value branches retain separate element masks.
  An undefined member or source element remains a hole after transport.
  Sentinel slices are descriptors, not fixed arrays.
- **Partial aggregate transport is silent.**
  Return, declaration, copy, assignment, by-value arguments, whole `@memcpy`,
  and optional wrap or unwrap report only an entirely proved-undefined value.
  These operations preserve precise holes and repair masks in the destination.
  A later selected read of a proved-undefined field, element, or byte reports.
  This includes selected reads after a call return or inside a source-proven by-value callee.
  Holes copied from container-level constants become UNKNOWN.
  A direct selected read on the constant still reports.
  UNKNOWN slots alone do not cause a diagnostic.
  An implicit receiver address does not read the aggregate payload.
  Opaque, extern, or unresolved results remain silent UNKNOWN values.
  A missing certificate alone does not establish undefined bytes.
  UNKNOWN values add no positive value, input, return, or payload certificates.
  Strict complete-payload certificates still require every element to be defined.
  Immutable constant tables require resolved declarations and initialized payloads,
  including nested elements. Every selector must fit its selected array extent.
  Constant indices and bounded unsigned modulo indices can prove this.
  An unsupported bound adds no positive destination initialization certificate.
  A complete vector or `@bitCast` payload certificate requires a complete source certificate.
  Its absence alone does not cause a diagnostic.
  Positive certificates do not map partial element coverage across different layouts.
  Casts keep the storage's lifetime origin. Diagnostic byte facts remain separate.
  Sentinel arrays have extra storage outside their logical extent.
  Logical coverage does not certify all bytes for `@bitCast`.
  A strict returned-array certificate requires body-definedness and covered inputs.
  Pointer types, integer addresses, and opaque extern returns prove no positive payload certificate.
- **Optional slice bindings retain their selected descriptor.**
  `const view = optional_slice orelse return` retains the source pointer
  and length on the non-null path, including fresh bindings in loops.
  A local backing array retains its element coverage and holes.
  Optional slice type information does not initialize its backing storage.
- **Runtime element writes retain precise diagnostic facts.**
  A defined runtime-index overwrite preserves existing coverage.
  It does not initialize other slots.
  A definite write with an UNKNOWN value removes prior holes from its selected location.
  It adds no positive defined-value certificate.
  A known-index undefined write creates an exact hole.
  An unresolved index retains facts about elements that may hold proved-undefined bytes.
  These rules also apply to fixed arrays stored in aggregate fields.
  A resolved `std.mem.swap` between two elements of the same complete
  array also preserves coverage. An arbitrary mutable-pointer call
  does not receive this guarantee.
  Source-proven element helpers and optional insertion helpers can
  preserve complete arrays when their actual inputs are defined.
  Preservation adds no positive initialization certificate to incomplete storage.
  Fixed-array pointer captures retain their owner for definite stores
  and for invalidation through opaque mutable aliases.
- **Read-only calls preserve coverage.** A resolved
  `std.mem.doNotOptimizeAway` does not write its input storage. Local
  functions with the same name and unresolved mutable-pointer calls do
  not receive this guarantee.
- **A loop must prove the region it writes.**
  The generic CFG permits zero iterations.
  Strict exhaustive certificates require a covering enumeration and an unconditional defined store.
  A bounded `0..array.len` fill can establish complete coverage.
  A runtime `0..count` fill establishes only its initialized prefix.
  Reads beyond that prefix report when the selected storage can still contain proved-undefined bytes.
  Conditional stores, nonzero starts, and interrupted loops do not establish complete certificates.
  A canonical zero-seeded counter loop can fill a fixed array on its normal exit.
  A fallible store gives no completion certificate on an error exit.
  A decrement-before-store countdown gives only its initialized prefix, not the unused suffix.
  Each strict proof checks current input definedness before it adds coverage.
  A failed proof alone does not cause a diagnostic.
- **Counted array fields retain their initialized prefix.**
  A source-proved append stores at the old count before it increments the count.
  Paths without an append must preserve both the array and its count.
  A zero default count proves an empty prefix, not a complete array.
  The count can be a local or a field path.
  A guarded read below that count does not read the unused suffix.
  Copies and optional returns retain the array/count relation within the copied value.
  A saved countdown cursor retains its own relation to the unchanged array.
  Selected stores, counter replacements, and mutable escapes revoke affected relations.
  Joins retain only relations that each incoming path proves.
  The join checks empty-count proofs before it removes path-specific bounds.
  Resolved unsigned cursor types retain these facts even without a written type annotation.
  By-value callees can read bounded prefix slices, including a minimum of two counts.
  These facts do not establish complete-array or returned-value certificates.
  An off-by-one read, a skipped store, or an undefined store still requires its own byte proof.
  Pointer-parameter fills require disjoint, non-escaped caller storage and a proved entry prefix.
  Each counter advance must follow its matching store, including in recursive callees.
  Returned enumeration indices are below a snapshot of the actual slice length taken before the call.
  Every successful return must select the same zero-based slice enumeration.
  Counter mutation cannot extend that saved prefix or change the saved length.
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
that writes `target[i] = …` with a by-pointer payload has a different shape.
Its write index does not establish an in-range fill certificate.
A missing certificate alone does not cause a diagnostic.

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

A selected read evaluates a field or element of the storage.
It reports if the selected bytes are proved undefined or can still hold proved-undefined values.
For example, `var out: [4]u8 = undefined; if (out[1] == 0)` reports.
Arithmetic, comparisons, and conditions also report proved-undefined inputs.
A bare `local[a..b]` builds a slice without reading the payload.
Its pointer and bounds still require their own diagnostic facts.
`&local`, `&local[i]`, and an implicit receiver address do not read the payload.
Taking an address does not initialize storage.
A resolved definite write initializes only its destination paths diagnostically.
The stored value needs no positive certificate to remove prior destination holes.
If the stored value is proved undefined, the destination receives those holes.
Strict source and payload certificates remain separate.

Whole-value transport reports when any transported slot, field, or byte is proved undefined.
The same policy applies to return, value copy, declaration, assignment, and by-value arguments.
Transport preserves precise holes in the destination.
A selected read of a proved-undefined field or element still reports.
Strict initialization certificates are unchanged.

Reported: `@memcpy` copies an array with three proved-undefined elements.

    var out: [4]u8 = undefined;
    out[0] = 0;
    @memcpy(ptr[0..out.len], out[0..]); // reports

Silent: `src` is a pointer parameter whose payload is UNKNOWN, with no independent facts that prove undefined bytes.

    @memcpy(dst[0..4], src[0..4]); // silent: UNKNOWN source payload

Opaque, extern, unresolved, and uncertified sources remain silent UNKNOWN unless independent facts prove undefined bytes.
They earn no positive value, input, return, array-completeness, or payload certificates.
Pointer and slice headers remain separate from their backing storage.
UNKNOWN pointer-parameter pointees do not report merely because their payload lacks a certificate.
The destination of a write is not a read.

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

The guard proof does not apply to a read outside the re-tested guard.
It also rejects calls that can change an operand without a later restore,
including calls inside the establishing arm after its test.
Shadowing declarations and intervening `defer` or `errdefer` also prevent this proof.
These cases report only if the reachable read can contain proved-undefined bytes.

- **A read inside the arm of a conditional value that never runs.**
  `return if (live) 0 else scratch[0];` evaluates one arm, not the
  whole conditional.  Each arm is lowered as its own return under
  the assumption its condition makes, so a read that only the dead
  arm has never enters a state where it happens.  A read on the arm
  that DOES run reports only if it reads proved-undefined bytes.
  A reachable UNKNOWN input alone does not report.

## Related

- (none — this rule is distinct from the resource-tracking rules.)