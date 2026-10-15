# scope-push-pop-imbalance

A parser or other stateful function calls a scope-push method
(`pushScope`, `enterScope`, `pushContext`, etc.) without protecting its
rollback. An early return can leave the persistent stack one level too
deep. Method names select candidates; they do not establish ownership.

## Example

```zig
// BUG: popScope only called on the success path.
// An early return before it leaves the scope stack unbalanced.
pub fn parseBlock(p: *Parser) !void {
    try p.pushScope(.block);  // BUG: no defer for the pop
    const token = try p.next();
    if (token == .eof) return error.UnexpectedEof;  // early return — no pop!
    try p.parseStatements();
    p.popScope();             // only reached on success
}

// FIX: wrap the pop in defer so it fires on every exit path.
pub fn parseBlock(p: *Parser) !void {
    try p.pushScope(.block);
    defer p.popScope();
    const token = try p.next();
    if (token == .eof) return error.UnexpectedEof;
    try p.parseStatements();
}
```

Real-world instances include oven-sh/bun#31239, #31340, and #31231, where
parser functions pushed a scope but returned early via `?Option` before
calling the matching pop — causing the scope stack to underflow on
subsequent parses.

## Ownership and rollback

- A call that is itself the returned expression transfers the acquisition
  to the caller. The canonical call must resolve to a source body. A
  discarded acquisition followed by an unrelated return does not transfer it.
- An immediate `errdefer` is an error-path rollback candidate only when it
  uses the same receiver and key arguments. The resolved declarations must
  apply opposite unit mutations to the same parameter-rooted counter.
  The rule maps each formal root to its actual argument. Different formal
  names can identify the same caller object.
- Each mutation must be an outer-block statement. A conditional mutation,
  a second write, or an unknown call in either body prevents this proof.
  Counter-address helpers require separate return-provenance proof.
  An unresolved body gives no rollback certificate.
- An ordinary top-level `defer` containing a pop remains a lexical cleanup
  signal. The current token heuristic does not establish all-path,
  same-object cleanup for this older case.

## Review boundaries

Persistent CFG path snapshots, caller-owned environment handles, parser
state discarded with a local arena, and descriptor-owning queues are not
necessarily lexical scope stacks. Their ownership must be checked through
the exact source declarations and error paths. A push/pop spelling, an AST
type name, or the presence of a destructor is not that proof.

Queue ownership does not settle a later borrow. In particular,
`acquireLatest`, fallible reporting or upload work, and a non-deferred
`releaseFrame` can still leak a borrowed descriptor: owner teardown may
refuse while the borrow is outstanding. Do not suppress that path merely
because the original push transferred the descriptor.

The rule retains its older no-explicit-return and cleanup-function-name
heuristics. These are analysis limits, not ownership guarantees. A `try`
can exit without an explicit `return`, and a cleanup-like name does not
prove that a function balances a stack.

To suppress on a specific line, add a `// zbc-disable-line:scope-push-pop-imbalance` comment.
