# forced-unwrap-iterator-next

**Severity:** error  
**Category:** misc / panic  
**Tier:** 1 (token detection), with a source-backed lookahead proof

## What this checks

`.next().?` force-unwraps the result of an iterator's `next()` call.
Standard Zig iterators return `?T`, where `null` means the iterator is
exhausted.  Force-unwrapping with `.?` asserts at runtime that a value is
present.  When the iterator is already exhausted — e.g., the caller passed
fewer items than the function expects — this panics in Debug/ReleaseSafe
and invokes undefined behaviour in ReleaseFast.

## Example (fires)

```zig
fn processSeq(iter: *ArgIterator) u32 {
    const first = iter.next().?;   // panics if iter is already empty
    const second = iter.next().?;  // panics if only one argument was given
    return first + second;
}
```

## Fix

Use `orelse` to handle exhaustion gracefully:

```zig
fn processSeq(iter: *ArgIterator) !u32 {
    const first = iter.next() orelse return error.MissingArgument;
    const second = iter.next() orelse return error.MissingArgument;
    return first + second;
}
```

Or the loop form when the count is not fixed:

```zig
while (iter.next()) |val| {
    process(val);
}
```

## Source-backed lookahead

A successful lookahead can prove that one subsequent `next()` returns a value.
The rule resolves both calls to their exact declarations.
The receiver must name the same local binding at both calls.
The canonical argument map must bind both receiver parameters to that same expression.
Both declarations must have the same lexical container.
Method names such as `ahead`, `peek`, or `count` do not establish this proof.

The supported lookahead body must match the consuming body.
The consuming body may add one scalar increment deferred until its final return.
The lookahead call must have a complete read-only effect result.
An `orelse return`, unlabeled `orelse break`, or unlabeled `orelse continue` establishes the non-null result on the remaining path.

The proof follows the path to the unwrap.
A branch that returns or continues cannot invalidate a different path.
A storage assignment, unknown call, builtin call, or non-read-only call invalidates the observation.
This includes mutations through extra arguments and changes to backing storage.
The observation cannot cross an unexpanded loop or certify a second consumption.
A cleanup scope that can finish before the call refuses the proof.
Unexpanded switch paths also refuse it.
Query and source-load errors propagate.

First-result proofs use the same stability checks. They resolve the exact
consuming body and the receiver's literal initializer, or a constructor whose
only statement returns that literal. An initialized non-null optional field can
exclude the body's first `orelse return null`. An explicit nonempty array can
exclude its first `if (receiver.field.len == 0) return null`. Every other return
must have a resolved nonoptional value. Another nullable return refuses the
proof.

This proves the first result of the SDK split iterator from its initialized
index and source body, including empty input. Constructor and method names are
not certificates. Tokenizing an arbitrary string does not guarantee a result.
A process argument iterator has no unconditional program-name guarantee.
An empty Unix argument vector is possible.
Empty, runtime-sized, and already-consumed vectors remain unproved.

**Checkpoint limit:** The analyzer does not prove the first result of
`std.process.Args.Iterator.Posix`, even with `.remaining = &.{"exe"}`.
Its consuming body returns through `std.mem.sliceTo`.
That function uses generic return-type factories with comptime reflection
switches and `@Pointer` construction that the analyzer cannot fully resolve.
The rule keeps the warning when the return type remains unknown.
This is a precision limit, not proof that this nonempty vector is unsafe.

The SDK argument-vector type also depends on `@import("builtin").os.tag`.
Without the actual project builtin source, that type remains unknown.
Target configuration alone does not resolve the unsupported return-type factories.
The analyzer does not substitute its host, ABI, or build mode for the project target.

An enum-dependent type can select one switch arm only from the enum's actual
constant value. The shared comptime-value query follows immutable declarations
and explicitly supplied literal aggregate fields in their canonical frames.
It compares the exact enum identity and decoded tag, not the enum type alone.
Every case must be understood before a fallback arm can be selected. Mutable
storage, pointer reads, runtime selectors, cycles, and uncertain cases remain
unproved.

The SDK argument fixtures configure an in-memory document with the complete
builtin source embedded by their test compiler.
They pass that context through `testing.runRuleTypedWithContext`.
The ordinary typed runner still creates an unconfigured context.
The configured controls cover empty, runtime-sized, and already-consumed vectors.
A separate control preserves the warning when the target configuration is unknown.

Fixed-column input schemas do not establish iterator cardinality.
Malformed or truncated producer output remains unproved unless the source validates the required fields.

## Real-world instances

- oven-sh/bun#27415 — `seq` builtin called `.next().?` after consuming all
  flag arguments; when only flags were provided (no numeric args) the
  iterator was empty → unconditional panic.
- oven-sh/bun#27316 — `cmds_array.next().?` on a JS-supplied command array;
  an empty array caused an unconditional panic before any work was done.
