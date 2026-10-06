// return-arraylist-items — the capacity reads that are NOT the full-capacity
// proof.  Every function below reserves capacity, uses less of it, and hands
// the caller a slice that is shorter than the block behind it; a caller that
// frees that slice frees the wrong number of bytes and loses the rest.  All
// four must keep their finding, and they are the cases a widened read of the
// suppression would have to quiet by accident.
//
// COMPILE-ONLY.  This file models the defect, so it is analysed and compiled
// but never run: every case leaks its allocation by construction, which is
// the point of the case.

const std = @import("std");

// Bug — no comparison at all (oven-sh/bun#23885, `toUTF8AllocWithType`).
pub fn noComparison(gpa: std.mem.Allocator) ![]u8 {
    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
    list.appendAssumeCapacity('x');
    return list.items;
}

// Bug — the capacity is READ, to decide whether filling it is worth doing.
// Nothing says the buffer IS full, so the returned slice still covers less
// than the whole allocation.
pub fn capacityRead(gpa: std.mem.Allocator) ![]u8 {
    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
    if (list.capacity > 4) list.appendAssumeCapacity('x');
    return list.items;
}

// Bug — the comparison is there and it is the INEQUALITY, which says the
// opposite of what the caller needs.
pub fn inequality(gpa: std.mem.Allocator) ![]u8 {
    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
    list.appendAssumeCapacity('x');
    std.debug.assert(list.items.len != list.capacity);
    return list.items;
}

// Bug — the capacity is THIS list's and the length is ANOTHER list's.  The
// two agreeing says nothing about how much of THIS allocation the returned
// slice covers, so it is not the proof in either operand order.
pub fn acrossTwoLists(gpa: std.mem.Allocator, other: *std.ArrayList(u8)) ![]u8 {
    var list = try std.ArrayList(u8).initCapacity(gpa, 64);
    list.appendAssumeCapacity('x');
    std.debug.assert(other.capacity == list.items.len);
    return list.items;
}
