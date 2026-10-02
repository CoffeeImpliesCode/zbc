# memset-undef-after-len-truncation

This warning identifies an empty undefined fill after a proved slice-length decrease.
The fill cannot touch the removed elements.

## Example

```zig
pub fn shrink(self: *Self, new_len: usize) void {
    if (new_len >= self.items.len) return;
    self.items.len = new_len;
    @memset(self.items[new_len..], undefined);
}
```

The guard proves that the length decreases.
After the assignment, `self.items[new_len..]` is empty.

## Fix

Fill the removed range before you change the length.

```zig
pub fn shrink(self: *Self, new_len: usize) void {
    if (new_len >= self.items.len) return;
    @memset(self.items[new_len..], undefined);
    self.items.len = new_len;
}
```

A saved backing pointer and the original upper bound also preserve access to the removed range.

## Analysis boundary

- The assignment and fill must be adjacent statements in one block.
- Typed ranges or valid branch predicates must prove a strict length decrease.
- The fill value must be `undefined`.
- The destination must be an empty tail, or the whole slice after its length becomes zero.
- Append growth, saved backing-pointer ranges, and fills of retained elements do not meet this contract.

Unknown direction, intervening statements, and cross-function sequences remain unproved.
The warning has an `unknown` verdict. It is not a reproduced runtime failure.
