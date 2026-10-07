# struct-literal-multiple-try

Two or more `.field = try <expr>` assignments inside the same struct literal initializer. If the first `try` succeeds but the second `try` propagates an error, the allocation from the first expression leaks — `errdefer` cannot be placed inside a struct literal.

## What the rule checks

The rule fires when the pattern `. identifier = try` appears inside an initializer, and the next field assignment (after the comma) also starts with `. identifier = try`. It does not fire when:
- Only one field uses `try`
- The second field does not use `try` (no interleaved allocation risk)

## Ownership proofs

The rule does not report a value-only first result. This proof reads the
called file-level function's declared return type. It accepts scalars,
enums without cleanup methods, and structs with value-only fields and no
cleanup methods. It follows `const` type aliases in their declaring scope.
An alias to a struct with owned pointer or slice fields does not make
that struct value-only.

A separate proof covers a private helper whose allocator parameter receives
storage from a scoped standard-library arena at every recognized call.
The caller must construct the real `std.heap.ArenaAllocator` and place
`defer scope.deinit()` immediately after its declaration. The cleanup must
remain valid through the helper call.

Direct `@import("std")` expressions and `const` namespace or type aliases
can establish the arena's identity. The rule follows each alias in its
declaring scope. A custom `ArenaAllocator`, a caller-chosen `std` parameter,
or a custom namespace does not establish this identity. A method named
`allocator` or `deinit` is not sufficient evidence.

An explicit `*std.heap.ArenaAllocator` field preserves the same declaration
identity when its allocator is derived at the allocation site. A field typed
only as `std.mem.Allocator` does not establish this ownership contract.

For typed checks, the rule authenticates standard-library allocation
declarations and binds result storage to the allocator formal. Unmanaged
`std.array_hash_map` `clone` and `cloneContext` use the supplied allocator;
passing a proved arena therefore covers their fresh backing storage.
An unrelated arena argument, a managed map's stored general allocator, or
a project method named `clone` does not establish this proof.

Source helpers are checked in the resolved declaration's actual frame.
Every call that can acquire a non-value result must use proved arena
storage or have a body with the same proof. Scalar and void results do not
prove harmless effects: they can allocate through out-parameters or
captured storage. Such calls require a complete read-only effect
certificate or the same body check. Recursive edges retain the complete
callable identity, including generic bindings; all other edges must still
pass. Missing bodies and unknown effects remain unproved.
The check also visits nested operands in the first initializer: an
arena-allocated outer header cannot cover a payload allocated by a general
allocator while its arguments are evaluated. Copies of existing headers
do not acquire new storage.

Compiler intrinsics are checked by allocation capability, not by read-only
effects or result type. Atomics, arithmetic, casts, and memory copies cannot
acquire fresh storage. Calls in their operands still require the ownership
proof. A `@field` projection does not invoke its result; an enclosing function
call must still resolve and pass the same proof. `@call`, `@extern`,
`@wasmMemoryGrow`, frame intrinsics, and unknown builtins remain unproved.

Each first-initializer query owns its effect memo and one existing 50,000-step
allowance. Recursive helper depth remains bounded at 16. Completed helper
proofs retain the actual callable identity and are reused only within this
query. Declaration identity does not request a normal-cleanup summary; an
unrelated consumer's failed summary must not change allocation provenance.
Budget exhaustion propagates as incomplete rule analysis, not a leak finding.

## Why it matters

`errdefer` works at statement level — it is not legal inside a struct literal expression. This means:

```zig
return Ast{
    .extra_data = try parser.extra_data.toOwnedSlice(gpa),  // succeeds, allocates
    .errors     = try parser.errors.toOwnedSlice(gpa),       // fails → extra_data leaks
};
```

There is no way to insert `errdefer gpa.free(extra_data)` between the two `try` expressions. The fix is to bind each allocation to a named local variable at statement level, where `errdefer` can protect it.

## Real-world instance

- **ziglang/zig#23285** (`std.zig.Ast.parse`): The function returned a struct literal with two `try` fields. When the second `toOwnedSlice` call failed (OOM), the first slice was not freed. Fix: extracted each field into a local binding with `errdefer`.

## Fix

```zig
// Instead of (second try failure leaks first allocation):
return Ast{
    .extra_data = try parser.extra_data.toOwnedSlice(gpa),
    .errors     = try parser.errors.toOwnedSlice(gpa),
};

// Bind to locals with errdefer protection:
const extra_data = try parser.extra_data.toOwnedSlice(gpa);
errdefer gpa.free(extra_data);
const errors = try parser.errors.toOwnedSlice(gpa);
return Ast{ .extra_data = extra_data, .errors = errors };
```
