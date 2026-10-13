# borrowed-slice-into-stack-buffer-returned

A stack-local `var <buf>: [N]<T> = undefined;` is passed to an
aliasing parser (`SemanticVersion.parse`, etc.).  The parser
populates fields of the returned struct with slices INTO `<buf>`
(`.pre`, `.build`, etc.).  The returned struct is then `return`-ed
from the fn — but `<buf>` dies at fn return, leaving the caller
with a struct whose sub-slice fields dangle.

## Canonical bug (ziglang/zig#25713)

```zig
pub fn detectOsVersion() !SemanticVersion {
    var buf: [64]u8 = undefined;
    _ = try std.posix.sysctl(&mib, &buf, ...);
    const ver = SemanticVersion.parse(&buf);  // ver.pre/build alias buf
    return ver;
}
```

`SemanticVersion.parse(text)` does
`ver.pre = text[a..b]; ver.build = text[c..];` — both slices into
the input.  When `text` is a stack-local, those slices die at
function return.

## Fix

Strip the aliased sub-slices before returning, or clone them:

```zig
var stripped = ver;
stripped.pre = null;
stripped.build = null;
return stripped;
```

## Why the detector is precise

The rule follows returned storage through calls, local copies, and aggregate
fields. It distinguishes an address from an address-free value copy.
Scalar cell addresses belong to `stack-escape`. Derived pointer and slice
loans belong to this rule.

### Allocator backing storage

An allocator's context pointer is not necessarily its allocation storage.
`ArenaAllocator.allocator()` stores `&arena` in the allocator header.
The allocated bytes come from `arena.child_allocator`, not the local arena
struct. `DebugAllocator` uses its `backing_allocator` in the same way.
The detector authenticates these accessor declarations against the toolchain
source. An accessor name alone does not establish storage provenance.

Returning heap-backed slices together with a moved arena does not borrow the
current frame. Returning `&arena`, or an allocator header containing that
address, still borrows the local arena.

`FixedBufferAllocator` allocations follow its `buffer` field. A local array
there remains a stack loan. A caller-owned buffer does not borrow the current
frame merely because its allocator header is local. An arena or debug
allocator with a stack-backed child allocator retains that stack loan.
`stackFallback` can allocate from its inline local buffer and remains a
stack-storage provider.

Unresolved storage and mutation walks cannot establish that a heap allocator's
context pointer escaped. They retain its allocation backing channel instead.
This does not remove loans from directly returned allocator headers.

## Limitations

This rule detects frame-storage escapes, not every allocator lifetime error.
For example, freeing heap storage before returning it is a separate problem.
Deep copies must preserve loans carried by pointer-bearing elements.
