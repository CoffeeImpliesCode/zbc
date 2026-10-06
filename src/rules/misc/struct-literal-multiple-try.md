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
