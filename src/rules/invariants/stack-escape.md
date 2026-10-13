# stack-escape

Returning a pointer or slice into a function-local stack variable.
The storage is reclaimed when the function returns, so the caller
reads garbage (or, worse, a future frame's contents).

The rule reports only a proved storage dependency. Passing a local address
to a call does not prove that the call returns it. Opaque call results and
unresolved field chains stay silent. A copied scalar field, such as an AST
token index, does not borrow the scratch buffer used to obtain it. Returning
the complete view can still escape when its slices point into that buffer.
Explicit integer encodings of local addresses remain tracked.

Copying a pointer or slice element out of a local array copies the element's
stored payload. It does not take the address of the array. A by-value loop
capture follows that same rule, including when a helper stores it in a
returned aggregate. Returning a slice of the local array, an element address,
or an element whose payload points into a local buffer still escapes.

A helper that copies scalar pointee values into a returned aggregate does
not also copy the addresses used to read those values. The rule checks
the copied value before following its formal-to-actual storage mapping.

## Example

Incorrect:

    fn build() *const [3]u8 {
        var buf: [3]u8 = .{ 1, 2, 3 };
        return &buf;                    // ← &buf dies with the frame
    }

Fix — return by value, or take an output buffer:

    fn build() [3]u8 {
        return .{ 1, 2, 3 };
    }

## When this might be a false positive

- The local is `comptime` (or used only in a `comptime`-instantiated
  function) and its address is comptime-known.  zbc does not track
  `comptime` evaluation; if the function only runs at compile time,
  the rule doesn't apply.  Split the function so the comptime form
  is its own decl, or restructure to return by value.
- The "stack local" is actually a function parameter passed by
  reference, where the caller owns the storage.  zbc treats params
  as `.plain` by default — if you see this rule fire on a param,
  please file an issue.

## Related

- `arena-escape`: returning a borrow into a function-local arena.
- `heap-use-after-free`: the storage was on the heap and has been
  explicitly freed.
