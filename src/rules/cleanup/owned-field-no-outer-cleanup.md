# owned-field-no-outer-cleanup

A struct has a value-typed field whose type (declared in the same
file) exposes a cleanup method (`deinit` / `close` / `destroy` /
`free` / `stop` / `finalize` / `dispose`) — but the outer struct
itself exposes NO cleanup method.  Users who treat the outer as a
plain value silently leak the inner's owned non-memory resource
(file handle, socket, ref, mmap) when the outer goes out of scope.

This is the complement to
[`missing-deinit-on-composed-owner`](missing-deinit-on-composed-owner.md):

- *That* rule fires when `Outer.deinit` EXISTS but FORGETS to
  call `<self>.<field>.deinit(...)`.
- *This* rule fires when `Outer.deinit` is MISSING entirely.

Same family of bugs (resource leak via composition); different
source signal.

## Source-backed cleanup entry points

With typed source, the cleanup entry point need not be named `deinit`.
The detector recognizes an exact field destructor called by an owner method
or a function that receives that owner. Both the receiver container and the
callee declaration must match. A same-named field on another type is unrelated.

A local temporary needs an active `defer`, or paired error and normal cleanup.
An error-arm call alone does not prove cleanup after a successful handoff.
Inline cleanup counts only when it matches the entire small inner destructor,
including each actual argument's field path. Partial cleanup remains diagnostic.

Static allocator callbacks, reset-only interfaces, and scalar accounting closes
do not establish a resource destructor. A private, unreferenced declaration can
be excluded only when the source contains no reflective namespace exposure.
Unknown calls and unresolved custody do not establish these proofs.


## Bad

```zig
const FileHandle = struct {
    fd: i32,
    pub fn close(self: *FileHandle) void { _ = self; }
};

const Session = struct {
    handle: FileHandle,  // owns an OS file handle
    name: []const u8,
    // No deinit / close / etc. — caller has no way to release
    // `handle.fd` when a Session value is dropped.
};
```

## Good

```zig
const FileHandle = struct {
    fd: i32,
    pub fn close(self: *FileHandle) void { _ = self; }
};

const Session = struct {
    handle: FileHandle,
    name: []const u8,
    pub fn deinit(self: *Session) void {
        self.handle.close();
    }
};
```

## Why pointer / slice fields are excluded

The "owned pointer" vs "borrowed pointer" distinction isn't
visible at the type level in Zig — `*Inner` could be a borrow OR
an owned heap pointer.  Treating all pointer fields as owned
would produce many false positives.  Value-typed fields
(including `?T` optional values) are the cleanest "I own this"
signal.

## Only one report per struct

If `Outer` has multiple qualifying fields, the rule fires once
per outer (the first qualifying field).  The design gap is the
SAME: `Outer` exposes no cleanup, regardless of how many of its
fields need one.
