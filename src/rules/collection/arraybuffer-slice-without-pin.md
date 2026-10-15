# arraybuffer-slice-without-pin

This rule warns when a possible raw code-unit view crosses a possible
GC dispatch call. Method names alone do not prove GC ownership or effects.
Findings remain unknown warnings. Check the actual storage and lifetime
contracts before you apply a GC protection API.

Real-world: oven-sh/bun#31339, multiple instances.

## Why this matters

JSC's garbage collector can move or free managed buffers during any
call that re-enters the JavaScript engine.  A raw slice taken via
`.slice()` or `.utf8()` is a direct pointer into that managed buffer.
If GC runs between the slice call and the last use of the slice, the
pointer may be invalid.

## Canonical bug

```zig
const bytes = buffer.slice();           // raw ptr into GC-managed buffer
doSomethingThatCallsJS(vm, ...);        // may trigger GC → buffer may move
use(bytes);                             // UAF
```

## Fix

Pin the buffer before taking the slice and unpin it after the slice
is no longer needed:

```zig
var pinned = buffer.pin(globalObject);
defer pinned.unpin();
const bytes = pinned.slice();
doSomethingThatCallsJS(vm, ...);        // buffer is pinned — safe
use(bytes);
```

## Detection

The rule scans each function body for:

1. A `const/var NAME = recv.method()` binding where `method` is a
   raw-view method: `slice`, `utf8`, `latin1`, `utf16`, `utf16le`,
   `bytes`, `toSlice`, `toOwnedSlice`, or `constSlice`.
   The instantiated canonical callee's return type can exclude an array
   or slice of slice descriptors, such as `[]const [:0]const u8`.
   This is not a raw code-unit view. Error-union payloads are classified
   the same way. Import aliases retain the same type identity.
   Unknown results and raw `[]u8` or `[]u16` views remain candidates.

2. After the binding, any call that may invoke GC:
   - A direct `recv.method(` call where `method` is a known JSC
     dispatch method (`call`, `evaluate`, `resolve`, `reject`, etc.).
   - A bare `identifier(` call where the callee is a same-file function
     whose body calls a GC-trigger method.

3. FP suppression: if a `.pin(` call appears on the same buffer
   receiver between the slice binding and the GC call, the fire is
   suppressed.

## Ordinary argument vectors

`std.process.Args.toSlice` produces a vector of strings, not a raw
byte view. A later path operation does not make that vector a GC borrow.
The rule checks the resolved result type, not argument names or method
spellings.

This exclusion does not prove an arena lifetime contract. It does not
make arbitrary slices, custom buffers, or unresolved calls safe.
