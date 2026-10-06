# Test fixtures

Synthetic Zig sources demonstrating the canonical bug shape (and
control variants) for each rule.  Each file has both a "fires" case
and at least one "doesn't fire" control.

The fixtures double as integration-test inputs: run
`./zig-out/bin/zbc test/fixtures/<rule>.zig` to verify the rule
catches the synthetic bug.

## Mapping to rule modules

PR references throughout the codebase use the GitHub shorthand
`<owner>/<repo>#<number>` so that future fixtures from other Zig
repos (TigerBeetle, Zig itself, etc.) stay unambiguous next to
Bun's.

| Fixture | Rule | PR |
|---|---|---|
| `partial_union_write.zig` | `partial-union-write` | [oven-sh/bun#29422](https://github.com/oven-sh/bun/pull/29422) |
| `aliased_heap_dupe.zig` | `aliased-heap-dupe` | [oven-sh/bun#29910](https://github.com/oven-sh/bun/pull/29910) |
| `clobbered_by_struct_reset.zig` | `clobbered-by-struct-reset` | [oven-sh/bun#29854](https://github.com/oven-sh/bun/pull/29854) |
| `realloc_byte_count.zig` | `realloc-byte-count` | [oven-sh/bun#29452](https://github.com/oven-sh/bun/pull/29452) |
| `asymmetric_field_free.zig` | `asymmetric-field-free` | [oven-sh/bun#29853](https://github.com/oven-sh/bun/pull/29853) |
| `missing_errdefer_between_tries.zig` | `missing-errdefer-between-tries` | [oven-sh/bun#30169](https://github.com/oven-sh/bun/pull/30169), [ziglang/zig#22131](https://github.com/ziglang/zig/pull/22131), [tigerbeetle/tigerbeetle#3711](https://github.com/tigerbeetle/tigerbeetle/pull/3711) |
| `free_then_try_realloc.zig` | `free-then-try-realloc` | [oven-sh/bun#29968](https://github.com/oven-sh/bun/pull/29968) |
| `free_then_try_realloc_mysql.zig` | `free-then-try-realloc` (faithful MySQL repro, no `#`-private fields) | [oven-sh/bun#29968](https://github.com/oven-sh/bun/pull/29968) |
| `destroy_after_deinit_in_loop.zig` | `destroy-after-deinit-in-loop` | [oven-sh/bun#29879](https://github.com/oven-sh/bun/pull/29879) |
| `dead_errdefer_in_result_fn.zig` | `dead-errdefer-in-result-fn` | [oven-sh/bun#27706](https://github.com/oven-sh/bun/pull/27706) |
| `duplicate_errdefer.zig` | `duplicate-errdefer` | [tigerbeetle/tigerbeetle#2700](https://github.com/tigerbeetle/tigerbeetle/pull/2700) |
| `overwrite_without_deinit.zig` | `overwrite-without-deinit` | [oven-sh/bun#28633](https://github.com/oven-sh/bun/pull/28633), [oven-sh/bun#29864](https://github.com/oven-sh/bun/pull/29864), hexops/mach `d690814b` (setter-without-prior-free; mined commit, no PR) |
| `stack_fallback_escape.zig` | `stack-fallback-escape` | [ghostty-org/ghostty#9885](https://github.com/ghostty-org/ghostty/pull/9885) |
| `unreleased_refs_on_error.zig` | `unreleased-refs-on-error` | hexops/mach `sysgpu/vulkan.zig:1887` (mined; no PR).  Related Bun PRs covered after the loop-requirement relaxation (`pendingActivityRef`/`Unref` family): [oven-sh/bun#29329](https://github.com/oven-sh/bun/pull/29329), [oven-sh/bun#29900](https://github.com/oven-sh/bun/pull/29900), [oven-sh/bun#29901](https://github.com/oven-sh/bun/pull/29901), [oven-sh/bun#29907](https://github.com/oven-sh/bun/pull/29907), [oven-sh/bun#30119](https://github.com/oven-sh/bun/pull/30119), [tigerbeetle/tigerbeetle#3711](https://github.com/tigerbeetle/tigerbeetle/pull/3711) (Rust `Box::into_raw` leak on non-OK status — analogous shape) |
| `hashmap_getptr_rehash.zig` | `hashmap-getptr-rehash` | Zig std `HashMap` pointer-stability footgun (canonical class, no specific PR) |
| `arraylist_items_slice.zig` | `arraylist-items-slice` | Zig std `ArrayList.items` pointer-stability footgun (canonical class).  Additional real-world refs: [tigerbeetle/tigerbeetle#3337](https://github.com/tigerbeetle/tigerbeetle/pull/3337), [ziglang/zig#25105](https://github.com/ziglang/zig/pull/25105) (lzma2 appendLz UAF), [ghostty-org/ghostty#11931](https://github.com/ghostty-org/ghostty/pull/11931) (argIter.next slice past iterator) |
| `fd_write_after_close.zig` | `fd-write-after-close` | POSIX/Windows file-handle use-after-close (canonical class, no specific PR) |
| `slice_of_arena_into_heap.zig` | `slice-of-arena-into-heap` | arena-allocated slice stored into a non-arena container (canonical class, no specific PR) |
| `free_without_null_then_check.zig` | `free-without-null-then-check` | [oven-sh/bun#30148](https://github.com/oven-sh/bun/pull/30148), [oven-sh/bun#30176](https://github.com/oven-sh/bun/pull/30176), [oven-sh/bun#29983](https://github.com/oven-sh/bun/pull/29983), [oven-sh/bun#29988](https://github.com/oven-sh/bun/pull/29988) |
| `tagged_union_retag_with_old_payload_read.zig` | `tagged-union-retag-with-old-payload-read` | [tigerbeetle/tigerbeetle#3317](https://github.com/tigerbeetle/tigerbeetle/pull/3317), [tigerbeetle/tigerbeetle#2200](https://github.com/tigerbeetle/tigerbeetle/pull/2200) |
| `union_deinit_without_inert_reset.zig` | `union-deinit-without-inert-reset` | [ghostty-org/ghostty#2257](https://github.com/ghostty-org/ghostty/pull/2257), [ghostty-org/ghostty#8307](https://github.com/ghostty-org/ghostty/pull/8307) |
| `self_undefined_after_destroy.zig` | `self-undefined-after-destroy` | [tigerbeetle/tigerbeetle#2687](https://github.com/tigerbeetle/tigerbeetle/pull/2687) |
| `missing_errdefer_on_out_param.zig` | `missing-errdefer-on-out-param` | [ghostty-org/ghostty#10401](https://github.com/ghostty-org/ghostty/pull/10401), [ghostty-org/ghostty#10392](https://github.com/ghostty-org/ghostty/pull/10392) (prepKittyImage orphan map entry when `dupe` fails) |
| `reset_skips_pooled_resource_release.zig` | `reset-skips-pooled-resource-release` | [tigerbeetle/tigerbeetle#3436](https://github.com/tigerbeetle/tigerbeetle/pull/3436), [tigerbeetle/tigerbeetle#1734](https://github.com/tigerbeetle/tigerbeetle/pull/1734), [tigerbeetle/tigerbeetle#3686](https://github.com/tigerbeetle/tigerbeetle/pull/3686) (ResourcePool grid blocks — `block_unref` needed on reset/deinit) |
| `return_borrowed_payload.zig` | `return-borrowed-payload` | [ghostty-org/ghostty#8358](https://github.com/ghostty-org/ghostty/pull/8358), [ghostty-org/ghostty#7711](https://github.com/ghostty-org/ghostty/pull/7711) |
| `unreleased_factory_handle.zig` | `unreleased-factory-handle` | hexops/mach `ca08255e` + `3d4888f4` commits (mined; canonical class, no PR — Mach mirror has issues disabled) |
| `memset_undef_after_len_truncation.zig` | `memset-undef-after-len-truncation` | [ziglang/zig#25810](https://github.com/ziglang/zig/pull/25810), [ziglang/zig#25832](https://github.com/ziglang/zig/pull/25832) |
| `publish_then_touch_self.zig` | `publish-then-touch-self` | [oven-sh/bun#29128](https://github.com/oven-sh/bun/pull/29128), [oven-sh/bun#31177](https://github.com/oven-sh/bun/pull/31177), [oven-sh/bun#30185](https://github.com/oven-sh/bun/pull/30185) |
| `assert_on_untrusted_input.zig` | Not in the rule catalog | [tigerbeetle/tigerbeetle#3709](https://github.com/tigerbeetle/tigerbeetle/pull/3709), [tigerbeetle/tigerbeetle#3726](https://github.com/tigerbeetle/tigerbeetle/pull/3726), [tigerbeetle/tigerbeetle#2980](https://github.com/tigerbeetle/tigerbeetle/pull/2980), [oven-sh/bun#29731](https://github.com/oven-sh/bun/pull/29731) (Buffer#copy/#fill TOCTOU), [oven-sh/bun#30061](https://github.com/oven-sh/bun/pull/30061) (Buffer.concat getter-detach TOCTOU) |
| `missing_deinit_on_composed_owner.zig` | `missing-deinit-on-composed-owner` | [ziglang/zig#22683](https://github.com/ziglang/zig/pull/22683), [ziglang/zig#20192](https://github.com/ziglang/zig/pull/20192), [ziglang/zig#18651](https://github.com/ziglang/zig/pull/18651) |
| `borrowed_slice_into_out_param.zig` | `borrowed-slice-into-out-param` | [oven-sh/bun#30151](https://github.com/oven-sh/bun/pull/30151), [oven-sh/bun#30223](https://github.com/oven-sh/bun/pull/30223), [oven-sh/bun#25563](https://github.com/oven-sh/bun/pull/25563) |
| `defer_and_errdefer_free_overlap.zig` | `defer-and-errdefer-free-overlap` | [ghostty-org/ghostty#8249](https://github.com/ghostty-org/ghostty/pull/8249) |
| `sentinel_strip_free_size_mismatch.zig` | `sentinel-strip-free-size-mismatch` | [ghostty-org/ghostty#8886](https://github.com/ghostty-org/ghostty/pull/8886) |
| `move_out_without_restore.zig` | `move-out-without-restore` | [ziglang/zig#24452](https://github.com/ziglang/zig/pull/24452) |
| `deinit_order_violates_construction_dep.zig` | `deinit-order-violates-construction-dep` | [tigerbeetle/tigerbeetle#3732](https://github.com/tigerbeetle/tigerbeetle/pull/3732) |
| `borrowed_slice_into_stack_buffer_returned.zig` | `borrowed-slice-into-stack-buffer-returned` | [ziglang/zig#25713](https://github.com/ziglang/zig/pull/25713) |
| `ref_before_ownership_transfer.zig` | `ref-before-ownership-transfer` | [oven-sh/bun#30137](https://github.com/oven-sh/bun/pull/30137) |

## Re-fetching the actual pre-merge buggy files

The actual buggy files from each PR are too large to bundle (5–8k
lines each).  To replay any of them against zbc:

```bash
REPO=oven-sh/bun
PR=29422
BASE=$(gh pr view "$PR" --repo "$REPO" --json baseRefOid -q .baseRefOid)
FILE=src/http/Decompressor.zig    # adjust per PR
curl -sL "https://raw.githubusercontent.com/$REPO/$BASE/$FILE" -o /tmp/buggy.zig
./zig-out/bin/zbc /tmp/buggy.zig
```

Each commit message documents the file paths PR-by-PR.

## Encountered PRs for Layer-1 / inferred rules

Layer-1 CFG rules (`heap-use-after-free`, `heap-double-free`,
`use-undefined`, `interior-pointer-destroy`, `asymmetric-field-free`,
`heap-leak`, `dead-errdefer-in-result-fn`, `fd-write-after-close`)
don't have per-rule fixtures here — they were designed top-down
from the CFG / annotation model.  But mining surfaced real-world
PRs that exercise these shapes; recorded here for provenance:

- **`heap-use-after-free`**:
  [ghostty-org/ghostty#12463](https://github.com/ghostty-org/ghostty/pull/12463) (selection vs scrollback prune cross-thread),
  [ghostty-org/ghostty#8576](https://github.com/ghostty-org/ghostty/pull/8576) (test arena freed before reads),
  [ghostty-org/ghostty#10932](https://github.com/ghostty-org/ghostty/pull/10932) (kitty image cross-thread state read).
- **`heap-double-free`**:
  [ghostty-org/ghostty#9609](https://github.com/ghostty-org/ghostty/pull/9609) (tmux `.broken` state — already-freed buffer re-freed in deinit),
  [ghostty-org/ghostty#8512](https://github.com/ghostty-org/ghostty/pull/8512) (FreeType renderGlyph),
  [ghostty-org/ghostty#8068](https://github.com/ghostty-org/ghostty/pull/8068) (GTK quit re-disposed fcitx IME window).
- **`heap-leak`**:
  [oven-sh/bun#28761](https://github.com/oven-sh/bun/pull/28761) (AbortSignal.timeout extra ref),
  [oven-sh/bun#29881](https://github.com/oven-sh/bun/pull/29881) (X509 + BIO RAII),
  [oven-sh/bun#29855](https://github.com/oven-sh/bun/pull/29855) (TextDecoder UTF-16),
  [ziglang/zig#15372](https://github.com/ziglang/zig/pull/15372) (http.Client/Server header/body buffers),
  [ziglang/zig#13947](https://github.com/ziglang/zig/pull/13947) (ArrayList.toOwnedSlice errdefer ownership conflict),
  [ghostty-org/ghostty#12349](https://github.com/ghostty-org/ghostty/pull/12349) (kitty APC parser state),
  [ghostty-org/ghostty#7542](https://github.com/ghostty-org/ghostty/pull/7542) (Flatpak GError leaks).
- **`use-undefined`**:
  [tigerbeetle/tigerbeetle#3617](https://github.com/tigerbeetle/tigerbeetle/pull/3617) (Context init leaves `previous_request_instant` undefined),
  [tigerbeetle/tigerbeetle#3540](https://github.com/tigerbeetle/tigerbeetle/pull/3540) (init-to-0 then asserted unreached),
  [ziglang/zig#22423](https://github.com/ziglang/zig/pull/22423) (Target.Query partial init),
  [ziglang/zig#25472](https://github.com/ziglang/zig/pull/25472) (http test undefined buffer read),
  [ziglang/zig#21524](https://github.com/ziglang/zig/pull/21524) (Reader test undefined endian).
- **`interior-pointer-destroy`**:
  [oven-sh/bun#30882](https://github.com/oven-sh/bun/pull/30882) (synthetic-module specifier — bitwise-copied `BunString` over-derefs at destructor).
- **`asymmetric-field-free`**:
  [tigerbeetle/tigerbeetle#3686](https://github.com/tigerbeetle/tigerbeetle/pull/3686) (ResourcePool errdefer uses `allocator.free` while success path uses `block_unref` — mismatched ownership protocol).
- **`fd-write-after-close`**:
  [oven-sh/bun#27666](https://github.com/oven-sh/bun/pull/27666) (ReadFileUV `queueRead` OOM-catch missing `return` → `remainingBuffer()` after `onFinish`).
- **`dead-errdefer-in-result-fn`**:
  [oven-sh/bun#27666](https://github.com/oven-sh/bun/pull/27666) (`onRead` error path calls `finalize()` instead of `onFinish()`, skipping `doClose()` → fd leak).

## Unit tests

The synthetic patterns here are also encoded as inline `test "…"`
blocks in their respective rule modules (e.g. `realloc_byte_count.zig`).
Those run as part of `zig build test`; this directory's primary
role is documentation / integration smoke-testing.
