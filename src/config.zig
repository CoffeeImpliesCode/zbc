//! Project-tunable knobs.  Small by design — zbc is a focused
//! arena-escape checker for Zig source.  Two pattern lists let
//! projects declare what counts as arena creation/destruction in
//! their codebase (defaults match std.heap.ArenaAllocator).

const std = @import("std");

pub const Config = struct {
    /// Source-text substrings that classifyExpr treats as
    /// "this call mints a fresh arena."  First match wins.
    /// Substring match (not token-aware) — order from specific to
    /// least specific if you customize.
    arena_init_patterns: []const []const u8 = &.{
        "ArenaAllocator.init",
    },

    /// Source-text substrings for "this call kills the receiver
    /// arena."  Detected in lowerCallStmt — matching call shapes
    /// emit `.arena_kill` against the receiver local.
    arena_kill_patterns: []const []const u8 = &.{
        ".deinit(",
    },

    /// Source-text substrings for "this call returns a heap
    /// allocation."  Defaults cover std.mem.Allocator's surface.
    /// Matched as substrings of the full call expression.
    heap_alloc_patterns: []const []const u8 = &.{
        ".alloc(",
        ".allocSentinel(",
        ".create(",
        ".dupe(",
        ".dupeZ(",
        ".allocPrint(",
        ".allocPrintZ(",
    },

    /// Source-text substrings for "this call frees its first arg."
    /// The freed pointer is extracted from the call's args[0].
    heap_free_patterns: []const []const u8 = &.{
        ".free(",
        ".destroy(",
    },

    /// Which invariants to enforce.  zbc currently has exactly one
    /// — arena_escape (slice borrowed from function-local arena
    /// must not escape).  Kept as a list so future generic
    /// invariants can be added without breaking the CLI surface.
    enabled: []const Invariant = &all_invariants,
};

/// Invariants zbc enforces.  All generic — no language-domain
/// assumptions about parsers, ASTs, or any project-specific
/// vocabulary.
pub const Invariant = enum {
    /// A slice borrowed from a function-local arena must not be
    /// returned past the arena's death.  Catches the common
    /// "return a slice from per-call arena" mistake.
    arena_escape,
    /// A pointer or slice into a function-local stack variable must
    /// not be returned — the storage dies with the frame.
    stack_escape,
    /// A value initialized to `undefined` and never reassigned must
    /// not be returned (caller would receive garbage).
    use_undefined,
    /// A heap allocation must not be freed twice on any path.
    heap_double_free,
    /// A heap pointer must not be read or returned after it has
    /// been freed.
    heap_use_after_free,
    /// A value borrowed from an arena must not be read after the
    /// arena is deinit'd.  Complements arena_escape (which catches
    /// the special case of leaking the borrow past return).
    arena_use_after_kill,
    /// A heap allocation must be freed with the same allocator
    /// that produced it.  Catches the oven-sh/bun#29840 class:
    /// `mimalloc_arena.alloc(...)` then `default.free(...)` (UB
    /// under any reasonable allocator implementation).
    allocator_mismatch,
    /// Calling a destructor (`destroy` / `deinit` / etc.) on an
    /// interior pointer into a container's storage is UB under
    /// typical allocators.  Catches the oven-sh/bun#30166 class:
    /// `for (entries.items) |*r| r.destroy();`.
    interior_pointer_destroy,
    /// A type with a heap-creator method (`<x>.create(Self)`) has
    /// a destructor (finalize / deinit / destroy) that doesn't
    /// free `self` — every instance leaks the heap descriptor.
    /// Catches oven-sh/bun#29840 class: `ResolveMessage.create` allocates
    /// self via `allocator.create(...)` but `finalize()` never
    /// calls `allocator.destroy(this)`.
    heap_leak,
    /// An assignment to long-lived storage (`x.* = ...` or
    /// `obj.field = ...`) whose RHS is an anonymous struct literal
    /// `.{ .tag = <expr> }` where `<expr>` contains an early-exit
    /// (`try ...` or `catch return ...` / `catch |...| { ... return; ... }`).
    /// Zig writes the union tag to the result location BEFORE
    /// evaluating the payload, so on the error path the LHS is
    /// left with the new tag and the old/garbage payload bytes — a
    /// later read (often via an `errdefer this.deinit()`) sees a
    /// wild pointer.  Catches oven-sh/bun#29422 class.
    partial_union_write,
    /// A "dupe" function returns `T` by value via a bitwise copy
    /// (`var dup = this.*; return dup;`), and T has a heap-owning
    /// field signalled by an `<X>_allocated: bool` sibling — but
    /// the dupe doesn't either clear `<X>_allocated` or re-allocate
    /// `<X>` independently.  Both the source and the dupe now hold
    /// the same heap pointer with `<X>_allocated == true`, so the
    /// later frees from each side collide (UAF, then double-free).
    /// Catches oven-sh/bun#29910 class: `Blob.dupeWithContentType`.
    aliased_heap_dupe,
    /// A heap-owning field is assigned (`this.<X> = <expr>;`) and
    /// then `this.*` is overwritten with a struct literal that
    /// does NOT include `.<X>`, so `<X>` silently falls back to
    /// its declared default (usually `null` / `&.{}`).  The prior
    /// heap pointer is unreachable and never freed by `deinit()`
    /// (which checks the now-default value).  Catches oven-sh/bun#29854
    /// class: `PathWatcher.init` clobbered `this.resolved_path`.
    clobbered_by_struct_reset,
    /// A call to `<allocator>.realloc(slice, <expr> * @sizeOf(T))`
    /// — the new-length argument multiplies by `@sizeOf(T)` as if
    /// it were a byte count, but Zig's `Allocator.realloc` takes
    /// an ELEMENT count.  The allocation grows by `@sizeOf(T)×`
    /// the intended size on every call.  Catches oven-sh/bun#29452 class:
    /// `SmallList.tryGrow` over-allocated.
    realloc_byte_count,
    /// A type's destructor (`deinit` / `finalize` / `destroy`)
    /// mentions some same-typed sibling fields but omits others.
    /// E.g. fields `query_string_map: ?QueryStringMap` and
    /// `param_map: ?QueryStringMap` — destructor handles the
    /// first but forgets the second.  Catches oven-sh/bun#29853 class:
    /// `MatchedRoute.deinit` forgot to free `param_map`.
    asymmetric_field_free,
    /// `const X = try <Type>.<method>(...);` where `<Type>` has a
    /// `deinit` method, then a subsequent `try` in the same scope
    /// with NO `errdefer X.deinit();` between.  If the second
    /// `try` throws, X leaks (its deinit isn't reached).  Catches
    /// oven-sh/bun#30169 class: `node_fs` Symlink/Link/Rename.fromJS where
    /// `old_path` was leaked when `new_path = try PathLike.fromJS(...)`
    /// errored.
    missing_errdefer_between_tries,
    /// `<allocator>.free(X); X = try <allocator>.alloc(...);` —
    /// after the free, X points at freed memory.  If the `try`'s
    /// alloc fails, the function returns the error and `X` is
    /// still that dangling pointer — a later `deinit` (which
    /// expects an owned slice) frees it again, double-freeing /
    /// using freed memory.  Fix is to set `X = &.{};` (or
    /// `undefined`) between the free and the fallible realloc.
    /// Catches oven-sh/bun#29968 class: MySQLConnection.handleResultSet
    /// reallocating `statement.columns` without clearing first.
    free_then_try_realloc,
    /// A destructor (`deinit` / `finalize` / `destroy`) loops over
    /// `<list>.items` calling `<h>.deinit()` per item but never
    /// `<allocator>.destroy(<h>)` (or `.free(<h>)`).  When the
    /// list's element type is a heap-allocated pointer (e.g.
    /// `std.ArrayList...(*Handler)` with items minted via
    /// `allocator.create(Handler)`), the per-item destructor
    /// reclaims the item's fields but not its heap descriptor —
    /// every list item leaks its allocation.  Catches oven-sh/bun#29879
    /// class: `LOLHTMLContext.deinit` looped handlers and called
    /// `handler.deinit()` but never `allocator.destroy(handler)`.
    destroy_after_deinit_in_loop,
    /// A fn whose return type is a parameterized tagged union
    /// (`Result(T)`, `Maybe(T)`, …) — NOT a Zig error union
    /// (`!T`) — contains an `errdefer` in its body.  Zig's
    /// `errdefer` only runs on Zig error returns (`return
    /// error.X`); a `return .{ .err = e }` is a normal return,
    /// so the errdefer never fires.  Any cleanup it was meant
    /// to do silently leaks.  Catches oven-sh/bun#27706 class: CSS
    /// parsers with `Result(T)` return type and dead errdefer
    /// blocks.
    dead_errdefer_in_result_fn,
    /// Two `errdefer <X>.<cleanup>();` statements register the
    /// same cleanup against the same receiver in one fn body.  On
    /// the error path both fire — the cleanup runs twice and the
    /// second call hits its assert / double-frees / corrupts
    /// state.  Catches tigerbeetle/tigerbeetle#2700 class:
    /// `Command.init` registered `errdefer command.io.deinit()`
    /// twice; second `IO.deinit()` hit
    /// `assert(self.fd >= 0)` in `IoUring.deinit`.
    duplicate_errdefer,
    /// `<this>.<field> = <RHS>;` where `<field>`'s declared type
    /// has a `deinit` method — but no `<this>.<field>.deinit();`
    /// (or `.deref()` / `.free()`) appears in the preceding few
    /// statements.  Each reassignment leaks the prior allocation.
    /// Single-field counterpart to `clobbered-by-struct-reset`
    /// (whole-struct overwrite).  Catches oven-sh/bun#28633 /
    /// oven-sh/bun#29864 class: protocol decoders and re-execute
    /// paths overwriting heap-owning fields without cleanup.
    overwrite_without_deinit,
    /// `var <SF> = std.heap.stackFallback(N, <alloc>);` produces an
    /// allocator whose small allocations land in the *caller's*
    /// stack frame.  When a container built on `<SF>.get()` calls
    /// `.toOwnedSlice()` / `.toOwnedSliceSentinel()` / similar and
    /// the resulting slice escapes the function (return, out-param
    /// write, store in a non-local struct), the pointer dangles
    /// once the frame dies — intermittent UAF whenever the
    /// allocation stays under the fallback threshold.  Catches
    /// ghostty-org/ghostty#9885 class; same shape as
    /// ziglang/zig#16344.
    stack_fallback_escape,
    /// A loop body contains `<obj>.<addref>()` calls (where addref ∈
    /// {`reference`, `retain`, `addRef`, `addref`}) acquiring
    /// refcounted references, and the enclosing fn has a later `try`
    /// with no `errdefer` containing a release-class method call
    /// (`release` / `deref` / `unref` / `removeRef`).  On the try's
    /// error path the references taken in the loop leak.  Catches
    /// the `hexops/mach` sysgpu/vulkan.zig PipelineLayout.init class:
    /// `for (...) |bgl| bgl.manager.reference();` then `try
    /// vkd.createPipelineLayout(...);` — no errdefer releases the
    /// references on vulkan-create failure.
    unreleased_refs_on_error,
    /// `const <X> = <map>.getPtr(...);` (or `getOrPut`,
    /// `getOrPutValue`, `getOrPutAssumeCapacity`,
    /// `getOrPutAdapted`) borrows a pointer into the map's internal
    /// storage.  A subsequent `<map>.<mutate>(...)` on the SAME
    /// receiver — where mutate ∈ {`put`, `putAssumeCapacity`,
    /// `putNoClobber`, `putNoClobberAssumeCapacity`, `remove`,
    /// `removeByPtr`, `fetchPut`, `fetchRemove`, `swapRemove`} — may
    /// rehash the table and invalidate `<X>`.  A later read of
    /// `<X>` is a UAF against table storage.  Zig std's HashMap
    /// docs explicitly call out that pointers returned by `getPtr`
    /// / `getOrPut.value_ptr` are valid only until the next
    /// capacity-modifying call.
    hashmap_getptr_rehash,
    /// `const <X> = <list>.items;` borrows a slice over the list's
    /// heap-backed storage.  A subsequent `<list>.<mutate>(...)` on
    /// the SAME receiver (where mutate ∈ {`append`, `appendSlice`,
    /// `appendNTimes`, `insert`, `insertSlice`, `addOne`,
    /// `addManyAsSlice`, `addManyAsArray`, `resize`, `clearAndFree`,
    /// `deinit`}) may reallocate the backing storage and invalidate
    /// `<X>.ptr` — a later read/write through `<X>` is a UAF
    /// against list storage.  Sibling of [[hashmap-getptr-rehash]];
    /// `*AssumeCapacity` variants are deliberately excluded (no
    /// realloc by contract).
    arraylist_items_slice,
    /// `const <X> = &<list>.items[<idx>];` borrows a pointer to a
    /// specific element.  A subsequent grow call on the SAME list
    /// (append/insert/resize/etc.) may reallocate the backing buffer —
    /// `<X>` then dangles.  Sibling of [[arraylist-items-slice]];
    /// element-pointer variant.  oven-sh/bun#29483.
    arraylist_element_ptr,
    /// `for (<list>.items) |...| { ... <list>.<mutate>(...); ... }`
    /// — the loop iterates over a snapshot of `.items` while the
    /// body calls a method on the SAME list that reallocates or
    /// reorders the backing storage (append/resize/insert/
    /// swapRemove/etc., plus hashmap put/remove that rehash).
    /// The loop's slice borrow may dangle, skip elements, or
    /// double-visit elements.  Sibling of [[arraylist-items-slice]]
    /// which fires on `const X = list.items;` + later mutate +
    /// later use of X; this rule fires on the loop SHAPE directly.
    iterator_invalidation_mutation,
    /// `Thread.spawn(.{}, fn, .{ &<local> })` /
    /// `<pool>.spawn(fn, .{ &<local> })` — passing the address of
    /// a function-LOCAL into a spawned thread.  The thread out-
    /// lives the spawning fn's frame, so the local pointer dangles
    /// once the fn returns.  Skips `&<param>` (caller-supplied
    /// pointer, not a stack-frame leak from this frame) and
    /// `&<heap-local>` (when the local was heap-allocated).
    thread_spawn_local_pointer,
    /// `<local>.<field> = &<local>;` then `return <local>;` — the
    /// self-referential struct is COPIED on return; the field
    /// still holds the original stack address, which is invalid
    /// both during and after the copy.  Catches the "self-pointer
    /// in returned-by-value struct" footgun common when porting
    /// C / Rust code that uses intrusive self-references.
    self_pointer_in_returned_value,
    /// `const gop = try map.getOrPut(key);` followed by
    /// `gop.value_ptr.*` used as a READ without a prior check of
    /// `gop.found_existing`.  When `found_existing == false` the map
    /// inserted a new slot; `value_ptr.*` is uninitialised and reading
    /// it is undefined behaviour.  Write-only access (`gop.value_ptr.*
    /// = value;`) is safe without the check.
    getorput_unguarded_value_read,
    /// `const|var <X> = try <dir>.<opener>(...);` binds an OS file
    /// handle; `<X>.close();` invalidates it; any subsequent use of
    /// `<X>` (method call or field access) reads/writes through a
    /// dangling fd.  On POSIX the closed fd may be reassigned by
    /// the kernel before the stale use lands, silently routing the
    /// write to an unrelated file.  Openers: createFile / openFile
    /// / openDir / open / openat / accept / socket (and their `Z`
    /// variants).  Skips defer/errdefer close (fires at scope exit,
    /// after every other use) and close inside diverging branches
    /// (catch/if bodies).
    fd_write_after_close,
    /// A slice allocated through a function-local
    /// `std.heap.ArenaAllocator` is passed as data to a container
    /// method (`append` / `appendSlice` / `put` / etc.) whose
    /// allocator argument is NOT the arena's allocator — when the
    /// arena dies at fn exit, the container holds a dangling
    /// slice.  Complements `arena_escape` (escape via return) and
    /// `arena_use_after_kill` (read after deinit) by catching the
    /// third escape path: STORE into a longer-lived container
    /// during the arena's lifetime.
    slice_of_arena_into_heap,
    /// `<allocator>.destroy(<recv>.<field>);` / `.free(<recv>.<field>);`
    /// in a NON-destructor fn without a subsequent
    /// `<recv>.<field> = null;` (or `= &.{}`, `= .empty`, `= ...new`).
    /// The freed slot now holds a dangling pointer; a later
    /// `if (<recv>.<field>) |h| use(h);` passes the optional null-
    /// check and UAFs, or the struct's own `deinit` re-frees the
    /// dangling slot.  Catches oven-sh/bun#30148 / #30176 / #29983 /
    /// #29988 class.
    free_without_null_then_check,
    /// `<path> = .{ .<NewTag> = .{ ... <path>.<OldTag>... ... } };`
    /// — reading the old tag's payload while assigning a new tag to
    /// the same union.  Under Zig's x86_64 self-hosted backend
    /// the active-tag flip happens BEFORE the RHS evaluates, so the
    /// old payload read may see undefined / garbage.  LLVM hides
    /// this on aarch64.  Catches tigerbeetle/tigerbeetle#3317 +
    /// #2200 class (same file `src/lsm/scan_tree.zig`, same shape,
    /// 14 months apart).
    tagged_union_retag_with_old_payload_read,
    /// A `switch (<recv>.<field>)` arm `.<Tag> => |*v| <body>`
    /// where `<body>` calls a cleanup method on the payload
    /// (`v.deinit()` / `v.<sub>.deinit()` / `.free()` / `.release()`
    /// / `.deref()` / `.destroy()` / `.close()`) but does NOT
    /// retag `<recv>.<field>` to an inert variant.  In a fn named
    /// `reset` / `clear` / `end` (idempotent by convention) the
    /// next call fires the same arm and double-frees.  Catches
    /// ghostty-org/ghostty#2257 + #8307 class.
    union_deinit_without_inert_reset,
    /// `<alloc>.destroy(<X>);` immediately followed by `<X>.* = ...`
    /// or `<X>.<field> = ...` — the write hits freed memory.  The
    /// canonical TigerStyle invariant is overwrite-THEN-free:
    /// `<X>.* = undefined; <alloc>.destroy(<X>);` — this rule
    /// catches the inversion.  Catches tigerbeetle/tigerbeetle#2687
    /// class.
    self_undefined_after_destroy,
    /// Multi-step in-place struct-builder:
    /// `try <out>.<field>.<acquire>(...)` (where `<out>` ∈
    /// {`result`, `out`, `r`} and `<acquire>` ∈
    /// {`ensureTotalCapacity`, `init`, `append`, ...}) populates
    /// `<out>.<field>` but a later `try` runs with no `errdefer
    /// <out>.<field>.deinit(...)` registered.  Catches
    /// ghostty-org/ghostty#10401 class — distinct from existing
    /// `missing-errdefer-between-tries` which covers the binding-
    /// and-leak `const X = try Type.method()` shape.
    missing_errdefer_on_out_param,
    /// A struct's `deinit` releases owned pool / sub-allocator
    /// slots (`<obj>.<cleanup>(...)` where cleanup ∈ {`release`,
    /// `free`, `destroy`, `close`, `deinit`, `unref`, `deref`}),
    /// but the sibling `reset` method doesn't.  State is logically
    /// "freed" after `reset` but the slots are still held.
    /// Catches tigerbeetle/tigerbeetle#3436 + #1734 class.
    reset_skips_pooled_resource_release,
    /// `return switch (<expr>) { .<Tag1> => |v| v, .<Tag2> => |v|
    /// try alloc.dupe(u8, v), ... };` — sibling-arm asymmetry.
    /// One arm clones / allocates the payload to give the caller
    /// ownership; the other arm returns the captured payload bare,
    /// which is a slice/pointer borrowed from the caller's input.
    /// Catches ghostty-org/ghostty#8358 + #7711 class.
    return_borrowed_payload,
    /// GPU/refcounted-factory leak — `const <X> = [try]
    /// <device>.<create-method>(...)` returns a refcounted handle
    /// with initial refcount=1, but the fn body has no `defer
    /// <X>.release()` AND the handle isn't returned or stored as
    /// a struct field.  One ref leaks per call.  Catches hexops/mach
    /// examples (custom-renderer, glyphs/App.zig).  Distinct from
    /// `unreleased-refs-on-error` which is about loop-side addref
    /// without paired release.
    unreleased_factory_handle,
    /// A proved slice-length reduction precedes an empty undefined fill.
    /// The fill cannot touch the removed elements.
    memset_undef_after_len_truncation,
    /// `<chain>.<publish-method>(this);` (or `(self)`) where the
    /// chain or method suggests concurrent / cross-thread dispatch
    /// (`queue.push`, `thread_pool.dispatch`, `enqueueTaskConcurrent`,
    /// etc.), followed by any further use of `this`/`self` in the
    /// same scope.  The consumer thread may have freed `this`
    /// before the access lands → cross-thread UAF.  Catches
    /// oven-sh/bun#29128 + #31177 + #30185 class.
    publish_then_touch_self,
    /// Outer struct's `deinit` doesn't call `<self>.<field>.deinit(...)`
    /// for a field whose type (same file) ALSO exposes a deinit.
    /// The inner's owned non-memory resources (file handles,
    /// sockets, refs, mmaps) leak.  Catches ziglang/zig#22683
    /// class (StackIterator forgot to call ma.deinit → /proc fd
    /// leak); related to ziglang/zig#20192 and #18651.
    missing_deinit_on_composed_owner,
    /// Outer struct has a value-typed field whose type (same file)
    /// exposes a cleanup method (deinit/close/destroy/free/stop/
    /// finalize/dispose) — but the outer struct exposes NO cleanup
    /// method of its own.  Users who treat `Outer` as a plain value
    /// silently leak the inner's owned resource on drop.  The
    /// complement to `missing-deinit-on-composed-owner`: that rule
    /// fires when deinit EXISTS but is incomplete; this one fires
    /// when deinit is missing entirely.
    owned_field_no_outer_cleanup,
    /// `defer <X>.deinit()` (or `defer <alloc>.free(<X>)`) and a
    /// later write `<out>.* = ...<X>...` into a pointer-typed
    /// fn parameter — the out-param holds a dangling slice once
    /// the defer fires on return.  Catches oven-sh/bun#30151 +
    /// #30223 + #25563 class.
    borrowed_slice_into_out_param,
    /// `defer <alloc>.free(<X>);` + `errdefer { ... <lhs> = <X>; }`
    /// (resurrects X into a field) + a subsequent `try` — on
    /// error, errdefer fires (frees NEW, restores OLD into the
    /// field), then defer fires (frees OLD).  The field is now a
    /// dangling pointer.  Catches ghostty-org/ghostty#8249
    /// (`Atlas.grow`).
    defer_and_errdefer_free_overlap,
    /// `<alloc>.free(<X>.ptr[0..<X>.len])` (or `.ptr.?[0..len]`)
    /// hand-rolls a non-sentinel slice from a many-item-pointer.
    /// If `<X>` is `[:0]const u8` or another sentinel-terminated
    /// slice, the underlying allocation is len+1 bytes — the
    /// allocator's free-size check trips ("Allocation size N+1
    /// does not match free size N").  Catches
    /// ghostty-org/ghostty#8886.
    sentinel_strip_free_size_mismatch,
    /// `var <X> = <OBJ>.toArrayList(...)` (or similar move-out
    /// method that clears OBJ's state) + fallible op on <X> +
    /// no `defer <OBJ>.setArrayList(<X>);` between.  On error,
    /// X is dropped with partial allocation and OBJ is left
    /// holding cleared/stale state.  Catches ziglang/zig#24452
    /// class (`Io.Writer.Allocating.toOwnedSlice*`).
    move_out_without_restore,
    /// In a fn body, `<A> = <T>.init(&<B>, ...)` creates a dep
    /// edge B→A.  Later `<B>.deinit()` runs BEFORE `<A>.deinit()`
    /// — A's deinit may dereference its borrowed pointer to B,
    /// which is already torn down.  Catches
    /// tigerbeetle/tigerbeetle#3732 (manifest_log_fuzz).
    deinit_order_violates_construction_dep,
    /// A stack-local `var <buf>: [N]<T> = undefined;` is passed
    /// to an aliasing parser (`SemanticVersion.parse`, etc.),
    /// and the returned struct (whose sub-slice fields alias
    /// the buffer) is then `return`-ed.  The caller receives a
    /// struct whose `.pre`/`.build`-style fields point at the
    /// now-dead stack buffer.  Catches ziglang/zig#25713 class.
    borrowed_slice_into_stack_buffer_returned,
    /// `var iter = <map>.<iter-method>();` followed by
    /// `while (iter.next()) |...| { ... <map>.<mutate>(...) ... }` —
    /// modifying a HashMap (put / remove / clear / etc.) while
    /// iterating it via `iterator()` / `keyIterator()` /
    /// `valueIterator()` invalidates the iterator's internal cursor.
    /// Subsequent calls to `iter.next()` have undefined behaviour.
    hashmap_iter_mutation,
    /// `<recv>.<addref>()` (addref ∈ ref/retain/reference/addRef/
    /// addref) immediately before `init(<recv>, …)` — the caller bumps
    /// the refcount by 1, but the init-style callee takes ownership and
    /// decrements exactly once.  The extra ref is never balanced and
    /// the object leaks.  Fix: remove the addref, OR keep it and add a
    /// paired `defer <recv>.deref()`.  Catches oven-sh/bun#30137 class.
    ref_before_ownership_transfer,
    /// Inside `if (<recv>.<field>) |*<cap>| { … }`, a local `<ptr>`
    /// is derived from `<cap>` (mutable pointer to the optional
    /// payload).  The same block then contains an inline assignment
    /// `<recv>.<field> = …` (null or other) that destroys the storage
    /// `<ptr>` was pointing into.  Any subsequent use of `<ptr>` is a
    /// UAF.  Inline-clear variant of oven-sh/bun#29979.  The callee-
    /// clear variant is covered by heap-use-after-free (CFG-level).
    opt_capture_ptr_after_field_clear,
    /// Single-field tagged-union literal assignment where the payload
    /// expression contains `try`.  Under Zig's x86_64 self-hosted
    /// backend (post-0.15) the tag flip happens BEFORE the payload
    /// evaluates; if `try` propagates an error the tag is written
    /// but the payload remains from the previous variant.
    /// oven-sh/bun#29422.
    tagged_union_payload_early_exit,
    /// `const <ptr> = &<recv>.<field1>.<field2>` followed by
    /// `<recv>.<field1> = …` (variant change) followed by use of
    /// `<ptr>`.  After the variant change the payload storage `<ptr>`
    /// points into is repurposed; any use is a UAF.
    /// oven-sh/bun#29977.
    union_payload_ptr_after_variant_change,
    /// `<recv>.<field> = true` → function call → `<recv>.<field> =
    /// false`, where `<field>` contains `in_progress`.  If the
    /// function triggers re-entrant code that sets the flag back to
    /// `true`, the post-call `false` clobbers that new state.
    /// oven-sh/bun#29899.
    flag_reset_after_callback,
    /// `for (<recv>.items) |…| { … call() … }` where `call`
    /// transitively invokes an ArrayList-grow method.  The loop's
    /// implicit slice pointer is invalidated by the reallocation.
    /// oven-sh/bun#29981, #29483.
    slice_loop_reentrant_grow,
    /// `<recv>.pushScope(…)` (or enterScope/pushContext/etc.) without
    /// a matching `defer <recv>.popScope()` (or similar pop method),
    /// when the fn body has at least one early `return`.  Early returns
    /// exit without popping, leaving the scope stack one level too deep
    /// and causing underflows on subsequent calls.  Catches
    /// oven-sh/bun#31239 / #31340 / #31231 class.
    scope_push_pop_imbalance,
    /// A function registered as an at-exit or cross-thread callback
    /// (via add_exit_callback / addExitCallback / onExit / atexit /
    /// etc.) accesses mutable state via `self.` field accesses without
    /// a `is_main_thread()` / `isMainThread()` / `isCLIThread()` guard.
    /// When process exit is triggered from a worker thread, the callback
    /// runs there and races with main-thread teardown.
    /// Catches oven-sh/bun#31376 class.
    exit_callback_cross_thread,
    /// `var NAME: iN = EXPR` where N ∈ {8, 16, 32} (a narrow signed
    /// integer) and EXPR contains `.len`, OR NAME is subsequently used
    /// as an array subscript `[NAME`.  When the collection has more
    /// items than iN can represent, the index wraps — the loop never
    /// executes or runs in reverse.  Catches oven-sh/bun#31129
    /// (url_path reverse scan) and oven-sh/bun#31339 (SQL result) class.
    index_type_narrowing_wraparound,
    /// `.field = recv.field` inside a struct literal where the field
    /// name suggests a refcounted / heap-owned type (`name`, `str`,
    /// `string`, `ref`, `handle`, `buf`, `data`, `content`) and no
    /// ref-acquire method (`clone()` / `dupeRef()` / `ref()` / etc.)
    /// is called on `recv.field` in the surrounding tokens.  Both the
    /// source and the copy will call the destructor on the same
    /// allocation → double-decrement → SIGFPE or UAF.  Catches
    /// oven-sh/bun#30955 (Blob.name SIGFPE), oven-sh/bun#30991 (WTF
    /// string ref), oven-sh/bun#30882 (specifier dupe_ref) class.
    ref_counted_copy_without_dupe,
    /// `const bytes = buf.slice();` (or `.utf8()`, `.latin1()`,
    /// `.utf16()`, etc.) takes a raw pointer into a JSC-managed
    /// buffer.  A subsequent call that enters the JS engine (e.g.
    /// `vm.call(...)`, `vm.evaluate(...)`) may trigger GC, which can
    /// move or free the backing buffer.  Bytes now dangles.  Fix:
    /// call `.pin(globalObject)` before taking the slice and
    /// `.unpin()` after.  Catches oven-sh/bun#31339 class.
    arraybuffer_slice_without_pin,
    /// `self.remoteSettings orelse self.localSettings` uses the wrong
    /// fallback direction — the left-hand field is likely a peer-
    /// advertised value; when absent (null), the code falls back to
    /// the locally-configured limit, silently relaxing a security
    /// check.  The fallback should use the local limit directly.
    /// Catches oven-sh/bun#31129 class (h2_frame_parser.zig).
    optional_fallback_wrong_side,
    /// Inside a loop, `if (buf[i] == ESCAPE_CHAR) { i += 1; }` is
    /// immediately followed by an unconditional `i += 1;` without a
    /// preceding bounds guard `i + 1 < buf.len`.  If the escape char
    /// is the last byte, the skip pushes `i` to `buf.len`; the
    /// subsequent unconditional `+= 1` or the next iteration reads
    /// past the end.  Fix: add `i + 1 < buf.len and` before the array
    /// access in the if condition.
    /// Catches oven-sh/bun#31435 (fmt.zig JS syntax highlighter).
    escape_skip_without_bounds_recheck,
    /// A fn whose name contains "parse", "skip", "visit", or "scan"
    /// calls itself recursively without a stack-depth guard
    /// (`is_safe_to_recurse()` / `isSafeToRecurse()` /
    /// `isStackOverflow()`).  Deeply nested input (e.g. thousands of
    /// nested type expressions, statement blocks, or AST nodes) will
    /// exhaust the call stack and crash the process.
    /// Fix: add `if (!stack_check.is_safe_to_recurse()) return
    /// error.StackOverflow;` at the entry of the function.
    /// Catches oven-sh/bun#31361 / #31333 class.
    recursive_parse_without_stack_check,
    /// `buf[N..]` where `N` is a non-zero integer literal and no `buf.len`
    /// check appears in the fn body before the slice expression.  When
    /// `buf.len < N`, this is a safety-checked OOB trap (Debug/Safe) or
    /// undefined behaviour (ReleaseFast).  Common in parsers that slice off
    /// fixed-size prefixes ("--- a/", "HTTP/1.1 ", etc.) without validating
    /// that the input is at least N bytes long.  Fix: add
    /// `if (buf.len < N) return error.TruncatedInput;` before the slice.
    /// Catches oven-sh/bun#31227 / #31264 class.
    slice_from_fixed_offset_without_len_check,
    /// `x / c.len` or `x % c.len` where container `c` is not proven non-empty.
    /// Integer division/modulo by zero (empty `c`) is safety-checked illegal
    /// behaviour.  Suppressed when a dominating guard proves `c.len != 0` or
    /// `c` is a fixed array `[N]T`, N >= 1.
    divmod_by_len_without_nonempty_guard,
    /// `-value << N` where `value` is a signed integer variable and no
    /// `std.math.minInt` guard appears in the fn body.  When
    /// `value == minInt`, negation overflows in two's complement (wraps
    /// back to `minInt`); the subsequent left shift produces wrong output
    /// or undefined behaviour in ReleaseFast.  Fix: use `@bitCast` /
    /// `@as(u32, @intCast(value))` or add an explicit minInt check.
    /// Catches oven-sh/bun#10782 (sourcemap.zig encodeVLQ overflow).
    negate_then_shift_without_minint_check,
    /// `const <X> = try <reader>.readInt(...)` (or readU32 / readU64 /
    /// readByte / etc.) deserializes an integer from untrusted data, then
    /// `<recv>.<pos_field> = <X>` assigns it to a position/cursor/offset
    /// field without a preceding `if (<X> > <recv>.buffer.len) return
    /// error.CorruptData;`.  The unchecked cursor is later used to slice
    /// the buffer, causing an out-of-bounds trap (Debug/Safe) or memory
    /// disclosure (ReleaseFast).  Fix: validate `<X> <= buffer.len`
    /// before writing the cursor.  Catches oven-sh/bun#12105 class
    /// (lockfile.zig Buffers.readArray).
    readint_unchecked_position_assignment,
    /// `list.items[list.items.len] = value;` — writes one slot past the
    /// initialized region without ensuring capacity first.  When
    /// `items.len == capacity` (the ArrayList is exactly full), this
    /// writes into allocator bookkeeping bytes, producing a safety-checked
    /// OOB trap in Debug mode or silent heap corruption in ReleaseFast.
    /// Fix: `try list.ensureUnusedCapacity(1); list.appendAssumeCapacity(value);`.
    /// Catches oven-sh/bun#29982 class (toUTF16Alloc sentinel branch).
    arraylist_sentinel_write_without_capacity,
    /// `@intFromFloat(<expr>)` without a `@min` / `@max` / `std.math.clamp`
    /// guard wrapping the argument.  Timer values, peer-advertised delays, and
    /// GC-scheduler floats can be ±Inf or exceed the target integer's range —
    /// `@intFromFloat` panics in Debug/Safe and produces undefined behaviour
    /// in ReleaseFast for those inputs.
    /// Fix: `@intFromFloat(@min(@max(x, min_f), max_f))` or `std.math.lossyCast`.
    /// Catches oven-sh/bun#28364 + #29328 class.
    intfromfloat_without_clamp,
    /// `data.len < (a + b)` — bounds check where the sum `(a + b)` is
    /// computed in a narrower integer type (e.g. `u32`) and may wrap to a
    /// small value before comparison against the `usize` length.  The guard
    /// evaluates `false` for huge inputs, bypassing it.  Fix: subtract to
    /// keep everything in `usize`: `data.len - a < b`; or explicitly widen:
    /// `@as(usize, a) + @as(usize, b)`.
    /// Catches oven-sh/bun#30157 class (IPC message decoder u32 wraparound).
    int_sum_overflow_in_bounds_cmp,
    /// `.ptr[0..N]` for N ∈ {2, 3, 4} bypasses Zig's slice length check.
    /// If the source slice has fewer than N bytes, this reads past the
    /// end of the allocation — silent OOB read in ReleaseFast, or memory
    /// disclosure / corruption.  Add a `if (slice.len < N) return error.Truncated`
    /// guard before using `.ptr` for a fixed-size window.
    /// Catches oven-sh/bun#29999 class (CodepointIterator.next: `.ptr[0..4]`
    /// without checking `bytes.len >= 4` at end-of-input).
    ptr_slice_without_bounds_check,
    /// `recv.lock()` called a second time on the same receiver without a
    /// preceding `recv.unlock()`.  `std.Thread.Mutex` is non-reentrant:
    /// a second `lock()` on the same thread deadlocks in ReleaseFast
    /// (spins forever) and asserts in Debug.  Unlock before re-acquiring.
    /// Catches oven-sh/bun#28907 class (ThreadPool sync deadlock).
    mutex_double_lock,
    /// `recv.lock()` released by a later `recv.unlock()`, but a `return`
    /// / `try` in between can exit with the lock held — leaking it (next
    /// acquirer deadlocks).  Use `defer recv.unlock();` after locking.
    lock_held_across_early_exit,
    /// `@ptrFromInt(0)` creates a null pointer to a non-nullable type.
    /// Dereferencing it is undefined behaviour on every platform:
    /// traps in Debug/ReleaseSafe, silent corruption in ReleaseFast.
    /// Use `?*T` with `null` for a sentinel or `usize` for offset arithmetic.
    ptrfromint_zero,
    /// `_ = allocator.resize(slice, new_len)` discards the boolean that
    /// indicates whether in-place growth succeeded.  When resize returns
    /// false the slice is still at the old length; writing beyond it is OOB.
    /// Fix: use `realloc` or capture the bool and fall back on false.
    resize_result_discarded,
    /// `errdefer X.deinit()` (or .deref/.free/.release) remains armed
    /// after an ownership-taking constructor call receives `X` as an
    /// argument.  A subsequent `try` triggers the errdefer even though `X`
    /// is now owned by the constructor → double-free.  Fix: reset
    /// `X = .{}` (or the type's inert sentinel) immediately after the
    /// constructor call to disarm the errdefer.
    /// Catches oven-sh/bun#28495/#28592/#29081/#29643/#29656/#30169/#30437/#30465
    /// class (8 PRs — S3/node_fs/CSS constructors taking ownership of paths).
    errdefer_alive_after_ownership_transfer,
    /// `@as(f32, @floatFromInt(expr))` narrows an integer to f32.  f32 only
    /// represents integers exactly up to 2²⁴ (16,777,216); larger values are
    /// silently rounded, defeating bounds checks and size arithmetic.  Use
    /// `@as(f64, @floatFromInt(…))` instead, or clamp first if f32 is required.
    /// Catches oven-sh/bun#30134 (CSS parser typed-array offset bounds checks).
    f32_narrowing_int_to_float,
    /// `[std.math.maxInt(T)]SomeType` declares `maxInt(T)` slots, leaving
    /// index `maxInt(T)` out of bounds when the array is later indexed by a
    /// value of type T.  Correct form: `[std.math.maxInt(T) + 1]SomeType`.
    /// Catches oven-sh/bun#29976 (hex_table[255] OOB) and
    /// #29973 (sort_table[std.math.maxInt(u8)] OOB).
    array_maxint_off_by_one,
    /// `@intCast(@max(expr, std.math.maxInt(T)))` uses `@max` to clamp
    /// before narrowing — but `@max` returns the *larger* operand, so values
    /// exceeding `maxInt(T)` are passed through and `@intCast` panics/wraps.
    /// The correct builtin is `@min`.
    /// Catches oven-sh/bun#29813 (queueSize clamped with @max instead of @min).
    intcast_clamp_uses_max,
    /// `.next().?` force-unwraps an iterator's optional result.  When the
    /// iterator is exhausted (e.g., the caller provided fewer items than
    /// expected), this panics in debug/safe builds and invokes UB in
    /// ReleaseFast.  Use `orelse <handler>` or `while (iter.next()) |v|`.
    /// Catches oven-sh/bun#27415 (seq builtin) and #27316 (cmds_array).
    forced_unwrap_iterator_next,
    /// `x < A and x > B` — an impossible range check that uses `and` instead
    /// of `or`.  No value can be simultaneously less than A and greater than B
    /// (when A ≤ B), so the guard body is permanently dead code.
    /// The correct out-of-range check is `x < A or x > B`.
    /// Catches oven-sh/bun#25905 (3 copy-paste dead RangeError guards).
    impossible_range_and,
    /// `@intCast(std.time.milliTimestamp())` — casting a signed i64 timestamp
    /// directly to an unsigned integer.  Negative timestamps (from clock skew
    /// or VM resets) panic in debug/safe builds and wrap to huge values in
    /// ReleaseFast.  Use `@intCast(@max(0, std.time.milliTimestamp()))`.
    /// Catches oven-sh/bun#10365 (PRNG seed from raw milliTimestamp).
    intcast_signed_timestamp,
    /// `@truncate(a - b)` or `@truncate(recv.field - other)` where the
    /// unsigned subtraction is not guarded by `a >= b`.  When `b > a` the
    /// subtraction wraps to a huge value BEFORE `@truncate` narrows it,
    /// yielding a garbage result.  Fix: add `if (a >= b)` guard, or use
    /// saturating subtraction `-|`.
    /// Catches oven-sh/bun#23993 (OKPacket.zig) and
    /// oven-sh/bun#6761/#29905 (h2_frame_parser.zig) class.
    truncate_subtraction_without_guard,
    /// `initCapacity(allocator, size + N)` where `N` is a small integer
    /// literal and `size` is a variable.  Plain `+` overflows when `size` is
    /// near `maxInt(usize)`, wrapping the requested capacity to a small value
    /// — the allocation succeeds but writes beyond its end corrupt the heap.
    /// Fix: use saturating add `+|` so the capacity caps at `maxInt(usize)`.
    /// Catches oven-sh/bun#29284 (read_file.zig) and
    /// oven-sh/bun#26999 (cron parser) class.
    initcapacity_plain_add_overflow,
    /// `buf[idx - 1]` where `idx` is an identifier without a visible
    /// `idx > 0` (or `idx != 0`) guard before the subscript.  When `idx`
    /// is `usize` and equals `0`, the subtraction wraps to `maxInt(usize)`,
    /// an OOB panic in Debug/Safe or silent arbitrary-memory read in
    /// ReleaseFast.  Fix: add a zero-guard before the expression.
    /// Catches oven-sh/bun#24561 (hosted_git_info.zig) and
    /// oven-sh/bun#28487 (braces.zig) class.
    index_minus_one_without_zero_guard,
    /// `if (COND) EXPR else 0 + ADDEND` — Zig's `if` has lower precedence
    /// than `+`, so this parses as `else (0 + ADDEND)`.  When COND is true,
    /// ADDEND is silently dropped from the result.  Causes capacity undercounts
    /// in hash-map and ArrayList pre-allocations, leading to `putAssumeCapacity`
    /// panics.  Fix: `(if (COND) EXPR else 0) + ADDEND` or
    /// `@intFromBool(COND) + ADDEND`.
    /// Catches oven-sh/bun#30466 and 20+ duplicate PRs (Bun.build crash with
    /// many `conditions`).
    else_literal_absorbs_addend,
    /// `catch |err| @panic(...)` — catching a named error and panicking turns
    /// a recoverable error into a process crash; use `try` to propagate or
    /// `catch unreachable` only when the error is provably impossible.
    /// Catches oven-sh/bun#30082 (S3 URL encode with fixed 1024-byte buffer).
    catch_error_panic,
    /// `.toUTF8(alloc).slice()` inline chain — the `LazyUTF8` temporary is
    /// freed at statement end, leaving the returned slice dangling.
    /// Catches oven-sh/bun#29600 (ResolveMessage UAF on referrer slice).
    toutf8_inline_slice_borrow,
    /// `@intCast(rc.int())` on a libuv return code — `.int()` returns `c_int`
    /// (32-bit) but the underlying result is `ssize_t` (64-bit); truncation
    /// causes a panic for I/O > 2 GB.
    /// Catches oven-sh/bun#29327 (Windows readFile panic on files > 2 GB).
    uv_return_value_intcast_truncation,
    /// `tryGet() orelse unreachable` on a JSRef — `tryGet()` returns null for
    /// finalized objects; `unreachable` produces SIGILL after finalization.
    /// Catches oven-sh/bun#29210 (valkey client SIGILL after finalize).
    tryget_orelse_unreachable,
    /// `@alignCast(expr.ptr)` — asserting alignment on a raw byte-slice pointer
    /// is unsafe; panics non-deterministically for network/file data at odd
    /// byte offsets.  Use `std.mem.readInt` or `@memcpy` into an aligned local.
    /// Catches oven-sh/bun#27082, #27281, #27384, #27290.
    aligncast_on_byte_slice,
    /// `@truncate(X.len)` — silently discards high bits of a slice length;
    /// user-controlled data ≥ 2^N bytes wraps to a garbage size, corrupting
    /// subsequent reads/allocs.  Catches oven-sh/bun#27443 (4 GB form body).
    truncate_len_to_narrow_int,
    /// `self.field = @as(T, @intCast(self.field))` — field assigned to itself
    /// through a cast is a no-op; almost always a copy-paste error where a
    /// freshly-computed local was intended.
    /// Catches oven-sh/bun#25905 (BufferReadStream.seek never advanced pos).
    field_self_assign_with_cast,
    /// `someCall(...).assert()` — chaining `.assert()` on the result of a
    /// fallible call converts every OS error into a process-crashing panic.
    /// In bun's codebase, `bun.sys.Maybe(T).assert()` panics when the variant
    /// is `.err`.  Catches oven-sh/bun#23344, #23520, #23935 (pipe start
    /// panicked on UV_ENOTCONN / UV_EPIPE after libuv error paths).
    maybe_assert_panics,
    /// `return list.items;` — returns the `.items` slice of a local
    /// `ArrayList` directly; the caller receives a `[]T` but has no
    /// `ArrayList` handle to free the backing allocation, leaking the
    /// capacity bytes.  Fix: `return list.toOwnedSlice();`.
    /// Catches oven-sh/bun#23885 (toUTF8AllocWithType capacity leak).
    return_arraylist_items,
    /// `<=` inside a `lessThan` comparator violates strict weak ordering —
    /// `lessThan(a, a)` returns `true` for equal elements, causing `std.sort`
    /// to loop indefinitely or produce incorrect output.
    /// Catches oven-sh/bun#24146 (sourcemap sort infinite loop).
    lessthan_uses_leq,
    /// `defer allocator.free(X)` appearing twice at the outermost level of the
    /// same function body — both defers fire at fn exit (LIFO), freeing X twice.
    /// Almost always a copy-paste error where a block was duplicated without
    /// removing the original defer.
    /// Catches oven-sh/bun#22978 (createArgv double-free of argv allocation).
    duplicate_defer_free,
    /// `map.getEntry(key).?` — forced optional unwrap on the `?Entry` result of
    /// `HashMap.getEntry`; panics when the key is absent.  Use
    /// `if (map.getEntry(key)) |e| { … }` or `orelse return`.
    /// Catches oven-sh/bun#14606 (H2 stream forced-unwrap after callback dispatch).
    hashmap_getentry_forced_unwrap,
    /// `@alignCast(x.?)` — forced optional unwrap inside an alignment assertion;
    /// two panic sources in one expression: `.?` panics on null, `@alignCast`
    /// panics on misalignment.  Use a non-optional type or guard with `orelse`.
    /// Catches tigerbeetle/tigerbeetle#3717 (io even_listen context cast).
    aligncast_on_optional_unwrap,
    /// Two consecutive `const VAR = STRUCT.FIELD orelse ...` declarations where
    /// STRUCT and FIELD are identical but VAR names differ — the second binding
    /// silently aliases the first instead of reading the intended field.
    /// Catches ziglang/zig#25099 (uri.user copied to both user and password).
    adjacent_decl_same_source_field,
    /// `@intCast(-VAR)` — negating a signed runtime integer before casting;
    /// if `VAR == minInt(T)` the negation overflows before the cast even runs.
    /// Use `@abs(VAR)` to safely take the magnitude.
    /// Catches ziglang/zig#23318 (fmtDurationSigned ns: i64 overflow).
    intcast_of_negated_signed,
    /// Two `.field = try <expr>` inside the same struct literal initializer;
    /// if the second `try` fails the first allocation leaks because `errdefer`
    /// cannot appear inside a struct literal expression.
    /// Catches ziglang/zig#23285 (Ast.parse extra_data + errors leak).
    struct_literal_multiple_try,
    /// `writeInt(NarrowType, @as(NarrowType, @truncate(EXPR)), endian)` —
    /// `@truncate` silently discards high bits of wider source values; use the
    /// correct wider type for `writeInt` or add a bounds check.
    /// Catches ziglang/zig#22233 (Elf.Atom dynAbs reloc truncation).
    writeint_truncated_value,
    /// `.items(.FIELD)[i].* = VALUE` on a MultiArrayList — `items(.field)`
    /// returns `[]FieldType` (values, not pointers); `[i].*` dereferences the
    /// field value as a memory address (UB).  Remove `.*` and assign directly.
    /// Catches ziglang/zig#22968 (ArrayHashMap setKey store_hash=true).
    multiarray_items_deref_assign,
    /// `startsWith(SLICE, "LITERAL")` followed by `SLICE[literal.len-1..]` —
    /// off-by-one strips one fewer character than the prefix; use
    /// `SLICE[literal.len..]` or `SLICE["LITERAL".len..]`.
    /// Catches oven-sh/bun#27970 (node_fs_watcher "file://" = 7 chars, used 6).
    startswith_strip_off_by_one,
    /// `(a + b) / 2` — classic binary-search midpoint overflow; if `a + b`
    /// exceeds the integer type's maximum the sum wraps before division.
    /// Use `a + (b - a) / 2` instead.  Catches zig#20029, zig#18718.
    midpoint_addition_overflow,
    /// `.allocator().free(X)` on an ArenaAllocator — free is a no-op; the
    /// arena only reclaims memory via `.deinit()`.  Catches bun#29380.
    arena_allocator_free_noop,
    /// `@memcpy(BASE[A..B], BASE[C..D])` — source and destination derive from
    /// the same slice and may overlap; @memcpy requires non-aliasing args.
    /// Use `std.mem.copyForwards` or `copyBackwards`.  Catches zig#21447.
    memcpy_overlapping_slices,
    /// `cmpxchgWeak(...) orelse break/return/continue` — logic inversion:
    /// null = success in Zig's cmpxchgWeak, so orelse exits on success not failure.
    /// Catches bun#28940 (ThreadPool spawn loop never spawned threads).
    cmpxchgweak_orelse_break,
    /// `buf[buf.len] = value` — write one past the end of a slice.
    /// Also catches `obj.field[obj.field.len] = value` (ArrayList `.items`).
    /// Catches bun#29982 (toUTF16Alloc null-terminator off-by-one).
    slice_write_at_len,
    /// `@max(x, std.math.maxInt(T))` or `@min(x, std.math.minInt(T))` — wrong
    /// clamping direction.  Ensures the value is ABOVE/BELOW T's range rather
    /// than within it.  Catches bun#29813 (@max → @min for queueSize clamp).
    clamp_wrong_direction,
};

pub const all_invariants: [112]Invariant = .{
    .arena_escape,
    .stack_escape,
    .use_undefined,
    .heap_double_free,
    .heap_use_after_free,
    .arena_use_after_kill,
    .allocator_mismatch,
    .interior_pointer_destroy,
    .heap_leak,
    .partial_union_write,
    .aliased_heap_dupe,
    .clobbered_by_struct_reset,
    .realloc_byte_count,
    .asymmetric_field_free,
    .missing_errdefer_between_tries,
    .free_then_try_realloc,
    .destroy_after_deinit_in_loop,
    .dead_errdefer_in_result_fn,
    .duplicate_errdefer,
    .overwrite_without_deinit,
    .stack_fallback_escape,
    .unreleased_refs_on_error,
    .hashmap_getptr_rehash,
    .arraylist_items_slice,
    .arraylist_element_ptr,
    .fd_write_after_close,
    .slice_of_arena_into_heap,
    .free_without_null_then_check,
    .tagged_union_retag_with_old_payload_read,
    .union_deinit_without_inert_reset,
    .self_undefined_after_destroy,
    .missing_errdefer_on_out_param,
    .reset_skips_pooled_resource_release,
    .return_borrowed_payload,
    .unreleased_factory_handle,
    .memset_undef_after_len_truncation,
    .publish_then_touch_self,
    .missing_deinit_on_composed_owner,
    .owned_field_no_outer_cleanup,
    .borrowed_slice_into_out_param,
    .defer_and_errdefer_free_overlap,
    .sentinel_strip_free_size_mismatch,
    .move_out_without_restore,
    .deinit_order_violates_construction_dep,
    .borrowed_slice_into_stack_buffer_returned,
    .iterator_invalidation_mutation,
    .thread_spawn_local_pointer,
    .self_pointer_in_returned_value,
    .getorput_unguarded_value_read,
    .hashmap_iter_mutation,
    .ref_before_ownership_transfer,
    .opt_capture_ptr_after_field_clear,
    .tagged_union_payload_early_exit,
    .union_payload_ptr_after_variant_change,
    .flag_reset_after_callback,
    .slice_loop_reentrant_grow,
    .scope_push_pop_imbalance,
    .exit_callback_cross_thread,
    .index_type_narrowing_wraparound,
    .ref_counted_copy_without_dupe,
    .arraybuffer_slice_without_pin,
    .optional_fallback_wrong_side,
    .escape_skip_without_bounds_recheck,
    .recursive_parse_without_stack_check,
    .slice_from_fixed_offset_without_len_check,
    .divmod_by_len_without_nonempty_guard,
    .negate_then_shift_without_minint_check,
    .readint_unchecked_position_assignment,
    .arraylist_sentinel_write_without_capacity,
    .intfromfloat_without_clamp,
    .int_sum_overflow_in_bounds_cmp,
    .ptr_slice_without_bounds_check,
    .mutex_double_lock,
    .lock_held_across_early_exit,
    .ptrfromint_zero,
    .resize_result_discarded,
    .errdefer_alive_after_ownership_transfer,
    .f32_narrowing_int_to_float,
    .array_maxint_off_by_one,
    .intcast_clamp_uses_max,
    .forced_unwrap_iterator_next,
    .impossible_range_and,
    .intcast_signed_timestamp,
    .truncate_subtraction_without_guard,
    .initcapacity_plain_add_overflow,
    .index_minus_one_without_zero_guard,
    .else_literal_absorbs_addend,
    .catch_error_panic,
    .toutf8_inline_slice_borrow,
    .uv_return_value_intcast_truncation,
    .tryget_orelse_unreachable,
    .aligncast_on_byte_slice,
    .truncate_len_to_narrow_int,
    .field_self_assign_with_cast,
    .maybe_assert_panics,
    .return_arraylist_items,
    .lessthan_uses_leq,
    .duplicate_defer_free,
    .hashmap_getentry_forced_unwrap,
    .aligncast_on_optional_unwrap,
    .adjacent_decl_same_source_field,
    .intcast_of_negated_signed,
    .struct_literal_multiple_try,
    .writeint_truncated_value,
    .multiarray_items_deref_assign,
    .startswith_strip_off_by_one,
    .midpoint_addition_overflow,
    .arena_allocator_free_noop,
    .memcpy_overlapping_slices,
    .cmpxchgweak_orelse_break,
    .slice_write_at_len,
    .clamp_wrong_direction,
};

pub const Default: Config = .{};

/// True iff `config.enabled` contains `inv`.
pub fn isEnabled(config: *const Config, inv: Invariant) bool {
    for (config.enabled) |e| {
        if (e == inv) return true;
    }
    return false;
}

/// Map a CLI-style name to its Invariant tag.  Returns null on
/// unknown names so callers can surface a useful error message
/// rather than silently ignoring typos.
pub fn invariantFromName(name: []const u8) ?Invariant {
    inline for (@typeInfo(Invariant).@"enum".fields) |field| {
        if (std.mem.eql(u8, name, field.name)) return @enumFromInt(field.value);
    }
    return null;
}

// ── Tests ──────────────────────────────────────────────────


test "invariantFromName round-trips every variant" {
    inline for (@typeInfo(Invariant).@"enum".fields) |field| {
        const got = invariantFromName(field.name).?;
        try std.testing.expectEqual(@as(Invariant, @enumFromInt(field.value)), got);
    }
}

test "invariantFromName returns null on unknown" {
    try std.testing.expectEqual(@as(?Invariant, null), invariantFromName("not_an_invariant"));
}
