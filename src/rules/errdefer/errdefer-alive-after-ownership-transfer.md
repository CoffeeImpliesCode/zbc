# errdefer-alive-after-ownership-transfer

**Severity:** error  
**Category:** errdefer / double-free  
**Analysis:** typed callee summary and scoped token walk

## What this checks

An `errdefer X.deinit()` remains armed after a call takes ownership of `X`.
A later `try` can propagate an error and invoke cleanup on the consumed resource.
The rule also recognizes `.deref`, `.free`, `.release`, `.close`, and `.destroy` cleanup.

The rule resolves the actual AST callee through `FileCache.actualCallSummaryAt`.
It requires an empty-root `normal_success_definite_freed_paths` certificate or a `retained_owned_params` cleanup certificate.
An immediate certificate proves argument release on every successful normal exit.
A retained certificate transfers cleanup responsibility while the resource remains live.
The rule maps every certified formal to its actual argument, including implicit and explicit receivers.
Constructor spelling, unresolved prototypes, and storage of a borrowed pointer do not establish ownership.
Conditional frees, error-return cleanup, and `errdefer` frees do not prove transfer after successful return.
Named-module identity remains part of callee resolution.
Source and allocation failures propagate instead of supplying a safe verdict.

## Example (fires)

```zig
const std = @import("std");

const Resource = struct {
    bytes: ?[]u8 = null,

    fn deinit(self: *Resource) void {
        if (self.bytes) |bytes| std.heap.page_allocator.free(bytes);
    }
};

fn discard(gpa: std.mem.Allocator, resource: *Resource) void {
    resource.deinit();
    gpa.destroy(resource);
}

fn later() !void {
    return error.Later;
}

fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
    errdefer resource.deinit();
    discard(gpa, resource); // The body proves that formal 1 is consumed.
    try later(); // The armed errdefer accesses the destroyed resource.
}
```

## Fix

Limit the cleanup to the period when the caller owns the resource.
For this example, a successful block exit expires the errdefer before the later fallible operation.

```zig
fn open(gpa: std.mem.Allocator, resource: *Resource) !void {
    {
        errdefer resource.deinit();
        discard(gpa, resource);
    }
    try later();
}
```

Where appropriate, assign an inert replacement immediately after transfer.
Its cleanup must be valid and must not release the transferred resource.
Do not remove cleanup for a constructor that only borrows the resource.

## Scope and proof

Fallible call arguments run before ownership transfers.
The rule checks later `try` expressions only while the registering block remains active.
An assignment to the cleanup local ends its tracked ownership state.
Nested function bodies do not execute at their declaration.

Retained storage needs a proven owning cleanup contract, not merely a field assignment.
For example, `TypeResolver.init` stores a borrowed context pointer and does not release that context in `deinit`.
The caller must retain its context errdefer for initialization failures.
