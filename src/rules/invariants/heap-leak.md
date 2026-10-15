# heap-leak

A type heap-allocates instances of itself (`allocator.create(Self)`)
but its destructor — `finalize` / `deinit` / `destroy` — never
calls `allocator.destroy(self)`.  Every instance is leaked: the
backing memory is reachable only through the heap pointer, and
nothing frees it.

This is the cross-method leak that per-fn analysis would normally
miss.  zbc detects it by inferring that the type is heap-self-
allocating from any constructor's body, then checking the
destructor's body for the missing `destroy(self)` call.

## Example

Incorrect — `ResolveMessage` is heap-allocated by `create()` but
`finalize()` only frees a sub-field, leaving `self` itself
leaked:

    const ResolveMessage = struct {
        allocator: std.mem.Allocator,
        msg: []u8,

        pub fn create(alloc: std.mem.Allocator, msg: []u8) *ResolveMessage {
            const this = alloc.create(ResolveMessage) catch unreachable;
            this.* = .{ .allocator = alloc, .msg = msg };
            return this;
        }

        pub fn finalize(self: *ResolveMessage) void {
            self.allocator.free(self.msg);
            // ← missing: self.allocator.destroy(self);
        }
    };

Fix — destructor must release the heap descriptor too:

    pub fn finalize(self: *ResolveMessage) void {
        self.allocator.free(self.msg);
        self.allocator.destroy(self);
    }

## When this might be a false positive

- An erased callback can recover its owner with a typed
  `@ptrCast(@alignCast(context))` and destroy that allocation.
  A callback for an embedded member can recover its containing
  allocation with `@fieldParentPtr`. Match the exact declaration,
  canonical owner type, allocation, and released storage. The callback
  parameter's spelling and the nearest named outer container are not
  ownership identities.
  For a same-address incoming-owner obligation, a source-bound callback
  certificate must release parameter zero through the SDK allocator.
  Its canonical released container must equal the callback's canonical
  lexical owner. An erased parameter type alone is not proof.
  A parent-container projection is a different relation: discharge
  requires the created canonical owner and its exact declared embedding
  field, not just an equal child type or a nearby constructor.
- Releasing a child, an adjacent object, or only one conditional
  outcome does not prove that the owner is released. Unknown callback
  effects do not prove cleanup. Actual allocation-leak controls must
  remain active.

## Related

- `heap-use-after-free`: the typical follow-on bug when the
  unfreed heap descriptor is later reached through a stale
  reference.
- `allocator-mismatch`: when the destructor frees with a
  different allocator than the one that allocated.
