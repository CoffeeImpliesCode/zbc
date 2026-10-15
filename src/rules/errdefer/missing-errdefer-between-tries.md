# missing-errdefer-between-tries

A heap-owning local is bound via `const X = try <Type>.<method>(...);`,
and a subsequent `try` in the same function appears with NO
`errdefer X.deinit();` registered between the binding and the
second `try`.  If the second `try`'s expression throws, Zig
propagates the error upward without running any cleanup for `X` —
the allocation leaks every time the second call fails.

The fix is to register the errdefer immediately after the binding:

    const old_path = try PathLike.fromJS(ctx, args) orelse …;
    errdefer old_path.deinit();
    const new_path = try PathLike.fromJS(ctx, args) orelse …;

## Example

Incorrect — `old_path` leaks if the second `PathLike.fromJS` throws:

    const old_path = try PathLike.fromJS(ctx, arguments) orelse {
        return ctx.throwInvalidArgumentTypeValue(...);
    };
    // ← missing: errdefer old_path.deinit();
    const new_path = try PathLike.fromJS(ctx, arguments) orelse {
        return ctx.throwInvalidArgumentTypeValue(...);
    };
    return .{ .old_path = old_path, .new_path = new_path };

Fix — register the errdefer immediately so the next failure cleans
up:

    const old_path = try PathLike.fromJS(ctx, arguments) orelse {
        return ctx.throwInvalidArgumentTypeValue(...);
    };
    errdefer old_path.deinit();

    const new_path = try PathLike.fromJS(ctx, arguments) orelse {
        return ctx.throwInvalidArgumentTypeValue(...);
    };
    errdefer new_path.deinit();

    return .{ .old_path = old_path, .new_path = new_path };

## Existing cleanup owners

An active `defer` or `errdefer` can protect the resource through a value copy:

    const opened = try dir.openFile(io, path, .{});
    var handle = opened;
    defer handle.close(io);
    const stat = try handle.stat(io);

The copy snapshots `opened`. The deferred call reads `handle` on exit.
Rebinding `handle` before the failing operation removes that proof; a separate
saved copy can still protect the original value. Same-spelled shadows and
captures from other branches do not protect it.

A private helper can also publish a handle into an owner's optional field.
The rule requires a complete, declaration-bound caller census. Every actual
owner must have active cleanup in the propagated error domain. The resolved
destructor must close that exact field or its optional payload. A public or
escaped helper, an unprotected caller, a different owner/field, an overwritten
slot, or an unknown rooted mutation does not supply this proof.

Method lookup uses the actual call expression, then maps its receiver to the
destructor's parameter. An optional capture retains the selected field's
identity. A later conditional discard may close that payload and clear the
slot, or leave it for the earlier close. Clearing the slot without closing
the payload invalidates the earlier cleanup; writing another field does not.

Cleanup registration is not cleanup execution. A deferred body is inspected
for an actual cleanup, not just a mention of the resource. A conditional
cleanup, cleanup registered after the later `try`, and cleanup in a block
that has already ended do not protect the failing operation. Later LIFO
actions must preserve the selected value or release it before replacement.
Passing a value to a fallible call alone does not prove ownership transfer.

## When this might be a false positive

- The type's `deinit` is a no-op (the value owns no heap), and the
  registered errdefer would just be noise.  Either remove the
  no-op deinit (so the rule stops considering the type heap-shape)
  or accept the rule's suggestion as a clarity improvement.
- The binding's call returns OWNED-BY-CALLEE values that the
  callee manages on error.  Rare — fromJS / parse / decode style
  fns conventionally hand ownership to the caller on success.

## Related

- `heap-leak`: the type-level version where a type's destructor
  itself fails to free `self`.
- `asymmetric-field-free`: a sibling-fields generalization of the
  destructor-completeness check.
