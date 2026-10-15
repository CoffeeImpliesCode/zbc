# slice-from-fixed-offset-without-len-check

**Severity:** error  
**Category:** bounds / OOB read  
**Tier:** 1 (token walk)

## What this checks

A slice expression `buf[N..]` where `N` is a non-zero integer literal is
used without a prior `buf.len >= N` guard in the same function body.  When
`buf` comes from user or network input whose length is unconstrained, and
`buf.len < N`, this is a safety-checked out-of-bounds trap (in Debug and
ReleaseSafe builds) or undefined behaviour (in ReleaseFast / ReleaseSafe
with `-fno-runtime-safety`).

## Example (fires)

```zig
fn parsePatchHeader(line: []const u8) ![]const u8 {
    // "--- a/path" header — skip the "--- a/" prefix (6 bytes)
    return line[6..]; // ← BUG: crashes if line.len < 6
}
```

## Fix

Validate the length before slicing:

```zig
fn parsePatchHeader(line: []const u8) ![]const u8 {
    const prefix_len = 6;
    if (line.len < prefix_len) return error.TruncatedHeader;
    return line[prefix_len..];
}
```

Or use `std.mem.startsWith` / `std.mem.indexOfScalar` and slice only on
confirmed matches.

## False positives and suppressions

- Suppressed if `buf.len` is accessed anywhere in the fn body before the
  slice — the programmer is already consulting the length.
- Suppressed if the buffer identifier is a chained field access
  (`self.buf[N..]`) — the receiver type provides more context that Tier 1
  cannot see; flag only at Tier 4 with ZLS type resolution.
- Not fired for `buf[0..]` — zero-offset open slices are always safe.
- The shared value-range oracle also checks the minimum length at the slice
  expression. It reads guarded allocation counts, fixed array extents, and
  checked helper return lengths. These facts describe the current slice
  header; a rebind or a call that can change that header invalidates them.
- An offset equal to the length is valid: the result is an empty suffix.
  A nonempty token therefore permits `[1..]`, but an iterator that can return
  an empty token does not establish that bound.
- A normal command-line invocation is not a proof that every supported
  launcher supplies `argv[0]`. Without an explicit nonempty argument contract,
  `argsAlloc` followed by `args[1..]` remains unproven.

The rule retains legacy token suppressions listed above. A source review of
one site does not establish that an entire file is safe.

## Real-world instances

- oven-sh/bun#31227 — `patch/lib.rs` Zig-mirror: `line[b"--- a/".len()..] `
  panics on a truncated `---/+++ ` patch header line where `line.len < 6`.
- oven-sh/bun#31264 — `eql_case_insensitive_ascii`: when `b` is shorter
  than `a`, reading `b[a.len()-1]` overruns the buffer.
