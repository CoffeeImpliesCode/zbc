# catch-error-panic

Reports a witnessed crash path that bypasses a matching, explicitly declared input-error result. Panic syntax alone does not prove that an error is recoverable.

## What the rule proves

The supported case requires all of this source evidence:

1. The caller is a file-scope function with one runtime `[]const u8` input and an explicit singleton error result, such as `error{BufferTooSmall}!void`.
2. Its body contains exactly a fixed local `[N]u8` buffer declaration initialized to `undefined`, followed by the caught call. There is no earlier guard, assertion, mutation, defer, or other operation that could establish an input precondition.
3. The existing resolver identifies the actual direct callee in the same source document and maps both arguments. The output is the local array's address; the input is the caller's slice parameter.
4. The callee takes `[]u8` output and `[]const u8` input parameters. Its first statement is `if (input.len > output.len) return error.BufferTooSmall;`, with the actual parameter identities and the same explicit error result as the caller.
5. The catch immediately invokes `@panic(...)` or the unshadowed `std.debug.panic(...)` from `@import("std")`.

This establishes a reachable input-dependent failure and a caller result that explicitly admits that failure. The diagnostic reports that this path crashes instead of returning the declared error. It does not infer the author's intent or claim that every input-dependent error must be recoverable.

```zig
fn copy(out: []u8, input: []const u8) error{BufferTooSmall}!void {
    if (input.len > out.len) return error.BufferTooSmall;
    @memcpy(out[0..input.len], input);
}

fn run(input: []const u8) error{BufferTooSmall}!void {
    var buffer: [1024]u8 = undefined;
    copy(&buffer, input) catch |err| @panic(@errorName(err));
}
```

Here, an input longer than the fixed buffer reaches the explicit error return and then the panic. The caller already declares that exact error in its output contract. Use `try copy(&buffer, input);` to preserve that contract, or validate the input before this call.

## Evidence limits

The rule requires typed source resolution. Inferred error sets, `anyerror`, error-set aliases, foreign or unresolved callees, generic transport, additional caller statements, and other error guards are outside this proof. Unknown results and analysis failures do not establish safety; resource and query errors propagate.

In particular, the rule does **not** certify these intentional fail-stop contracts:

- Returning an owned lease during a no-error destructor or while unwinding.
- Stopping cleanup before dependent resources are destroyed after a failed release or GPU drain.
- Failing a test through a callback or assertion helper that cannot return an error.
- Enforcing a whole-snapshot reservation across a no-error ABI.
- Failing a run when required final output cannot be written.

Those cases need ownership, callback, reservation, or output semantics that this rule does not prove. A `void` return, `defer`, test filename, function name, or panic message is neither a safety proof nor proof of a bug. The selected regression fixtures remain outside the proved input/result contract, not “proved safe.”

There is no message-based exemption: `@panic(@errorName(err))` still crashes. Naming the error does not make a reachable input failure impossible. `try`, `catch |err| return err`, and `catch unreachable` are not panic-call patterns. The last form asserts impossibility; safe modes check it at runtime, not as a compile-time proof.

## Historical motivation

The broader failure class includes oven-sh/bun#30082: fixed output buffers in S3 URL encoding were followed by panic-on-error handling, so sufficiently long input crashed the process. That history motivates checking input bounds. It is not a claim that the narrow source proof above covers every encoder or every intentional fail-stop policy.
