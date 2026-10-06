// return-arraylist-items — the full-capacity comparison, written both ways
// round.  When the function equates the list's used length with its own
// capacity before returning `.items`, the slice it hands back IS the whole
// allocation, so the caller can free it as it stands and the rule stays
// quiet.
//
// The two operands are different widths — `list.items.len` is five tokens
// and `list.capacity` is three — so each orientation has to be read at the
// offset its own spelling is written at.  A single shared offset only holds
// for the operand it was measured on, and reading the shorter one at the
// longer one's offset asks about the tokens standing in front of the
// operator rather than about the operand.
//
// This file is SAFE code and it runs: `main` builds each list to an exact
// capacity, checks the comparison holds under the spelling written here, and
// frees the returned slice with the allocator that owns it.  A finding on
// this file would be a false positive on provably balanced code.
//
// `initCapacity` reserves exactly the capacity asked for, which is what makes
// filling the list to its own capacity the ordinary way to write this.

const std = @import("std");

// Control 1 — the length on the left, the capacity on the right.
fn forward(gpa: std.mem.Allocator) ![]u8 {
    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
    for (0..64) |_| list.appendAssumeCapacity('x');
    std.debug.assert(list.items.len == list.capacity);
    return list.items;
}

// Control 2 — the same comparison written the other way round.
fn reverse(gpa: std.mem.Allocator) ![]u8 {
    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
    for (0..64) |_| list.appendAssumeCapacity('x');
    std.debug.assert(list.capacity == list.items.len);
    return list.items;
}

pub fn main() !void {
    const gpa = std.heap.page_allocator;

    const forward_bytes = try forward(gpa);
    const reverse_bytes = try reverse(gpa);
    if (forward_bytes.len != 64 or reverse_bytes.len != 64) return error.UnexpectedLength;

    // Each returned slice is the whole allocation, so freeing it with the
    // allocator that produced it is what balances the pair above.
    gpa.free(forward_bytes);
    gpa.free(reverse_bytes);
}
