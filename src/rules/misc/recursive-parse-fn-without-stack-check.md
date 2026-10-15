# recursive-parse-fn-without-stack-check

**Severity:** error  
**Category:** stack overflow / denial of service  
**Tier:** 1 (token walk, per-fn body)

## What this checks

A parser, visitor, or scanner function (name contains "parse", "skip",
"visit", or "scan") calls itself recursively without a stack-depth guard
such as `is_safe_to_recurse()`.  Adversarially deep input — thousands of
nested type expressions, statement blocks, or AST nodes — exhausts the call
stack and hard-crashes the process.

## Example (fires)

```zig
const Parser = struct {
    pub fn skipType(p: *Parser) void {
        // processes nested type — no guard
        while (p.peek() == '[') {
            p.advance();
            p.skipType();   // ← recursive call, no stack check
        }
    }
};
```

## Fix

Add a stack-overflow guard at the top of the function and return an error
(or report a diagnostic) when the stack is too deep:

```zig
const Parser = struct {
    stack_check: bun_core.StackCheck,

    pub fn skipType(p: *Parser) !void {
        if (!p.stack_check.is_safe_to_recurse())
            return error.StackOverflow;
        while (p.peek() == '[') {
            p.advance();
            try p.skipType();
        }
    }
};
```

Alternatively, thread a `depth: u32` parameter and return an error when
it exceeds a known-safe maximum.

## Guard evidence and limits

The rule recognizes a straight-line entry counter increment, a deferred
decrement of that exact counter, and a comparison that returns an error
before the recursive call. The comparison can follow the increment or
reside in a fallible entry helper. For the helper case, the canonical call
must resolve its source declaration. The rule maps the receiver formal to
the actual caller receiver and compares the exact counter field path.
The helper must increment that counter and then reject excessive depth.
No later helper work may reset the checked counter before successful return.
A method named `enter` alone is not a guard.

A `recursion_depth` meter label or observation is not a limit. In
particular, resetting state for each distinct subprogram call does not
bound the host stack across a deep acyclic chain. A byte-size limit on an
input frame also does not establish a safe container-nesting limit.

An AST walk can be bounded by its producer, but that requires a complete
caller and actual-value provenance proof. An AST type tag alone does not
prove that all incoming trees came from the capped parser. Nor does that
proof cover a walker that can enter another subprogram body.

The rule retains older compatibility heuristics for depth-named
parameters, explicit stack-check calls, visited-set checks, and explicit
recursion-entry calls. These are not general termination or stack-space
proofs. A visited set rejects cycles, not arbitrarily long acyclic paths.

## Real-world instances

- oven-sh/bun#31361 — `skip_typescript_type` / `skip_type_script_binding`
  in the transpiler lacked `is_safe_to_recurse()` guards; deeply nested
  TypeScript tuple types (e.g. `[[[...0...]]]` with tens of thousands of
  levels) would crash the process with a stack overflow.
- oven-sh/bun#31333 — `visit_stmt` / `print_stmt` / `print_if` lacked
  guards; a cascade of deeply nested `{ }` blocks or `else if` chains
  reached only by those passes (not the parser) would overflow.
