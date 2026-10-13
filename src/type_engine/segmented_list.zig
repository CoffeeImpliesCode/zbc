// https://github.com/ziglang/zig/blob/14fc4d481151d6ac0fb433d625cc97b4c2fe3eba/lib/std/segmented_list.zig
//
// The MIT License (Expat)
//
// Copyright (c) Zig contributors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

const std = @import("std");
const assert = std.debug.assert;
const testing = std.testing;
const mem = std.mem;
const Allocator = std.mem.Allocator;

// Imagine that `fn at(self: *Self, index: usize) &T` is a customer asking for a box
// from a warehouse, based on a flat array, boxes ordered from 0 to N - 1.
// But the warehouse actually stores boxes in shelves of increasing powers of 2 sizes.
// So when the customer requests a box index, we have to translate it to shelf index
// and box index within that shelf. Illustration:
//
// customer indexes:
// shelf 0:  0
// shelf 1:  1  2
// shelf 2:  3  4  5  6
// shelf 3:  7  8  9 10 11 12 13 14
// shelf 4: 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30
// shelf 5: 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62
// ...
//
// warehouse indexes:
// shelf 0:  0
// shelf 1:  0  1
// shelf 2:  0  1  2  3
// shelf 3:  0  1  2  3  4  5  6  7
// shelf 4:  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
// shelf 5:  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
// ...
//
// With this arrangement, here are the equations to get the shelf index and
// box index based on customer box index:
//
// shelf_index = floor(log2(customer_index + 1))
// shelf_count = ceil(log2(box_count + 1))
// box_index = customer_index + 1 - 2 ** shelf
// shelf_size = 2 ** shelf_index
//
// Now we complicate it a little bit further by adding a preallocated shelf, which must be
// a power of 2:
// prealloc=4
//
// customer indexes:
// prealloc:  0  1  2  3
//  shelf 0:  4  5  6  7  8  9 10 11
//  shelf 1: 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27
//  shelf 2: 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59
// ...
//
// warehouse indexes:
// prealloc:  0  1  2  3
//  shelf 0:  0  1  2  3  4  5  6  7
//  shelf 1:  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
//  shelf 2:  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
// ...
//
// Now the equations are:
//
// shelf_index = floor(log2(customer_index + prealloc)) - log2(prealloc) - 1
// shelf_count = ceil(log2(box_count + prealloc)) - log2(prealloc) - 1
// box_index = customer_index + prealloc - 2 ** (log2(prealloc) + 1 + shelf)
// shelf_size = prealloc * 2 ** (shelf_index + 1)

/// This is a stack data structure where pointers to indexes have the same lifetime as the data structure
/// itself, unlike ArrayList where append() invalidates all existing element pointers.
/// The tradeoff is that elements are not guaranteed to be contiguous. For that, use ArrayList.
/// Note however that most elements are contiguous, making this data structure cache-friendly.
///
/// Because it never has to copy elements from an old location to a new location, it does not require
/// its elements to be copyable, and it avoids wasting memory when backed by an ArenaAllocator.
/// Note that the append() and pop() convenience methods perform a copy, but you can instead use
/// addOne(), at(), setCapacity(), and shrinkCapacity() to avoid copying items.
///
/// This data structure has O(1) append and O(1) pop.
///
/// It supports preallocated elements, making it especially well suited when the expected maximum
/// size is small. `prealloc_item_count` must be 0, or a power of 2.
pub fn SegmentedList(comptime T: type, comptime prealloc_item_count: usize) type {
    return struct {
        const Self = @This();
        const ShelfIndex = std.math.Log2Int(usize);
        // `dynamic_segments` is a list of shelf pointers, so its length is a shelf
        // *count*, and a count is one more than the largest shelf index a list can
        // address: a list big enough to fill shelf `maxInt(ShelfIndex)` owns that
        // shelf plus every shelf below it.  Counts are therefore `usize` — the type
        // of `dynamic_segments.len`, `len` and `new_capacity` — and are never
        // narrowed to `ShelfIndex`; only `shelfSize` does that, where the shift
        // needs it.
        comptime {
            // Proving the domain of `shelfCount` here means a later edit cannot
            // reintroduce a list whose shelf count the shelf index type cannot
            // address — the case that `maxInt(usize)` boxes exercise.
            assert(shelfCount(std.math.maxInt(usize)) <= @as(usize, 1) << @bitSizeOf(ShelfIndex));
        }

        const prealloc_exp: ShelfIndex = blk: {
            // we don't use the prealloc_exp constant when prealloc_item_count is 0
            // but lazy-init may still be triggered by other code so supply a value
            if (prealloc_item_count == 0) {
                break :blk 0;
            } else {
                assert(std.math.isPowerOfTwo(prealloc_item_count));
                const value = std.math.log2_int(usize, prealloc_item_count);
                break :blk value;
            }
        };

        prealloc_segment: [prealloc_item_count]T = undefined,
        dynamic_segments: [][*]T = &[_][*]T{},
        len: usize = 0,

        pub const prealloc_count = prealloc_item_count;

        fn AtType(comptime SelfType: type) type {
            if (@typeInfo(SelfType).pointer.is_const) {
                return *const T;
            } else {
                return *T;
            }
        }

        pub fn deinit(self: *Self, allocator: Allocator) void {
            self.freeShelves(allocator, self.dynamic_segments.len, 0);
            allocator.free(self.dynamic_segments);
            self.* = undefined;
        }

        pub fn at(self: anytype, i: usize) AtType(@TypeOf(self)) {
            assert(i < self.len);
            return self.uncheckedAt(i);
        }

        pub fn count(self: Self) usize {
            return self.len;
        }

        pub fn append(self: *Self, allocator: Allocator, item: T) Allocator.Error!void {
            const new_item_ptr = try self.addOne(allocator);
            new_item_ptr.* = item;
        }

        pub fn appendSlice(self: *Self, allocator: Allocator, items: []const T) Allocator.Error!void {
            for (items) |item| {
                try self.append(allocator, item);
            }
        }

        pub fn pop(self: *Self) ?T {
            if (self.len == 0) return null;

            const index = self.len - 1;
            const result = uncheckedAt(self, index).*;
            self.len = index;
            return result;
        }

        pub fn addOne(self: *Self, allocator: Allocator) Allocator.Error!*T {
            const new_length = self.len + 1;
            try self.growCapacity(allocator, new_length);
            const result = uncheckedAt(self, self.len);
            self.len = new_length;
            return result;
        }

        /// Reduce length to `new_len`.
        /// Invalidates pointers for the elements at index new_len and beyond.
        pub fn shrinkRetainingCapacity(self: *Self, new_len: usize) void {
            assert(new_len <= self.len);
            self.len = new_len;
        }

        /// Invalidates all element pointers.
        pub fn clearRetainingCapacity(self: *Self) void {
            self.len = 0;
        }

        /// Invalidates all element pointers.
        pub fn clearAndFree(self: *Self, allocator: Allocator) void {
            self.setCapacity(allocator, 0) catch unreachable;
            self.len = 0;
        }

        /// Grows or shrinks capacity to match usage.
        /// TODO update this and related methods to match the conventions set by ArrayList
        pub fn setCapacity(self: *Self, allocator: Allocator, new_capacity: usize) Allocator.Error!void {
            if (prealloc_item_count != 0) {
                // The preallocated segment and the shelves together hold
                // `2 ** (prealloc_exp + shelf_count)` boxes.  With a preallocated
                // segment a list owns at most one shelf less than the largest shelf
                // index, so this shift stays in range.
                const capacity: usize = @as(usize, 1) << (@as(usize, prealloc_exp) + self.dynamic_segments.len);
                if (new_capacity <= capacity) {
                    return self.shrinkCapacity(allocator, new_capacity);
                }
            }
            return self.growCapacity(allocator, new_capacity);
        }

        /// Only grows capacity, or retains current capacity.
        pub fn growCapacity(self: *Self, allocator: Allocator, new_capacity: usize) Allocator.Error!void {
            const new_cap_shelf_count = shelfCount(new_capacity);
            const old_shelf_count = self.dynamic_segments.len;
            if (new_cap_shelf_count <= old_shelf_count) return;

            const new_dynamic_segments = try allocator.alloc([*]T, new_cap_shelf_count);
            errdefer allocator.free(new_dynamic_segments);

            var i: usize = 0;
            while (i < old_shelf_count) : (i += 1) {
                new_dynamic_segments[i] = self.dynamic_segments[i];
            }
            errdefer while (i > old_shelf_count) : (i -= 1) {
                allocator.free(new_dynamic_segments[i][0..shelfSize(i)]);
            };
            while (i < new_cap_shelf_count) : (i += 1) {
                new_dynamic_segments[i] = (try allocator.alloc(T, shelfSize(i))).ptr;
            }

            allocator.free(self.dynamic_segments);
            self.dynamic_segments = new_dynamic_segments;
        }

        /// Only shrinks capacity or retains current capacity.
        /// It may fail to reduce the capacity in which case the capacity will remain unchanged.
        pub fn shrinkCapacity(self: *Self, allocator: Allocator, new_capacity: usize) void {
            if (new_capacity <= prealloc_item_count) {
                self.freeShelves(allocator, self.dynamic_segments.len, 0);
                allocator.free(self.dynamic_segments);
                self.dynamic_segments = &[_][*]T{};
                return;
            }

            const new_cap_shelf_count = shelfCount(new_capacity);
            const old_shelf_count = self.dynamic_segments.len;
            assert(new_cap_shelf_count <= old_shelf_count);
            if (new_cap_shelf_count == old_shelf_count) return;

            // freeShelves() must be called before resizing the dynamic
            // segments, but we don't know if resizing the dynamic segments
            // will work until we try it. So we must allocate a fresh memory
            // buffer in order to reduce capacity.
            const new_dynamic_segments = allocator.alloc([*]T, new_cap_shelf_count) catch return;
            self.freeShelves(allocator, old_shelf_count, new_cap_shelf_count);
            if (allocator.resize(self.dynamic_segments, new_cap_shelf_count)) {
                // We didn't need the new memory allocation after all.
                self.dynamic_segments = self.dynamic_segments[0..new_cap_shelf_count];
                allocator.free(new_dynamic_segments);
            } else {
                // Good thing we allocated that new memory slice.
                @memcpy(new_dynamic_segments, self.dynamic_segments[0..new_cap_shelf_count]);
                allocator.free(self.dynamic_segments);
                self.dynamic_segments = new_dynamic_segments;
            }
        }

        pub fn shrink(self: *Self, new_len: usize) void {
            assert(new_len <= self.len);
            // TODO take advantage of the new realloc semantics
            self.len = new_len;
        }

        pub fn writeToSlice(self: *Self, dest: []T, start: usize) void {
            const end = start + dest.len;
            assert(end <= self.len);

            var i = start;
            if (end <= prealloc_item_count) {
                const src = self.prealloc_segment[i..end];
                @memcpy(dest[i - start ..][0..src.len], src);
                return;
            } else if (i < prealloc_item_count) {
                const src = self.prealloc_segment[i..];
                @memcpy(dest[i - start ..][0..src.len], src);
                i = prealloc_item_count;
            }

            while (i < end) {
                const shelf_index = shelfIndex(i);
                const copy_start = boxIndex(i, shelf_index);
                const copy_end = @min(shelfSize(@as(usize, shelf_index)), copy_start + end - i);
                const src = self.dynamic_segments[shelf_index][copy_start..copy_end];
                @memcpy(dest[i - start ..][0..src.len], src);
                i += (copy_end - copy_start);
            }
        }

        pub fn uncheckedAt(self: anytype, index: usize) AtType(@TypeOf(self)) {
            if (index < prealloc_item_count) {
                return &self.prealloc_segment[index];
            }
            const shelf_index = shelfIndex(index);
            const box_index = boxIndex(index, shelf_index);
            return &self.dynamic_segments[shelf_index][box_index];
        }

        /// The number of shelves needed to hold `box_count` boxes.
        ///
        /// The result is a count, not a shelf index: the shelf that
        /// `maxInt(ShelfIndex)` addresses still needs an entry of its own in
        /// `dynamic_segments`, so the count does not fit in `ShelfIndex`.
        fn shelfCount(box_count: usize) usize {
            if (prealloc_item_count == 0) {
                // ceil(log2(box_count + 1)) is one more than
                // floor(log2(box_count)) for every non-empty list, which is
                // written this way so that a list holding `maxInt(usize)`
                // boxes does not overflow `box_count + 1`.
                if (box_count == 0) return 0;
                return @as(usize, std.math.log2_int(usize, box_count)) + 1;
            }
            // ceil(log2(box_count + prealloc_item_count)) - prealloc_exp - 1 is
            // floor(log2(box_count + prealloc_item_count - 1)) - prealloc_exp.
            // Taking the `- 1` first keeps `box_count + prealloc_item_count`
            // from overflowing, and a total past `maxInt(usize)` has the same
            // log2 as `maxInt(usize)` itself.  A list that fits in the
            // preallocated segment owns no shelf at all, which the `+ 1`
            // spells out: `log2_int` rejects a zero argument.
            const total = std.math.add(usize, @max(box_count, 1), prealloc_item_count - 1) catch std.math.maxInt(usize);
            return @as(usize, std.math.log2_int(usize, total)) - @as(usize, prealloc_exp);
        }

        /// The number of boxes in shelf `shelf`.
        ///
        /// `shelf` is a shelf index — a `shelfIndex` result, or a counter
        /// walking the shelves of a list — which never exceeds
        /// `maxInt(ShelfIndex)`, but the counters that walk shelf counts hold
        /// it in a `usize`.  Narrowing it here is what keeps the shifts below
        /// in range, and the conversion is checked so that a shelf count which
        /// ever did exceed the largest shelf index traps instead of wrapping.
        fn shelfSize(shelf: usize) usize {
            const shelf_index = std.math.cast(ShelfIndex, shelf) orelse
                @panic("SegmentedList shelf index is out of range");
            if (prealloc_item_count == 0) {
                return @as(usize, 1) << shelf_index;
            }
            return @as(usize, 1) << (shelf_index + (prealloc_exp + 1));
        }

        fn shelfIndex(list_index: usize) ShelfIndex {
            if (prealloc_item_count == 0) {
                return std.math.log2_int(usize, list_index + 1);
            }
            return std.math.log2_int(usize, list_index + prealloc_item_count) - prealloc_exp - 1;
        }

        fn boxIndex(list_index: usize, shelf_index: ShelfIndex) usize {
            if (prealloc_item_count == 0) {
                return (list_index + 1) - (@as(usize, 1) << shelf_index);
            }
            return list_index + prealloc_item_count - (@as(usize, 1) << ((prealloc_exp + 1) + shelf_index));
        }

        fn freeShelves(self: *Self, allocator: Allocator, from_count: usize, to_count: usize) void {
            var i = from_count;
            while (i != to_count) {
                i -= 1;
                allocator.free(self.dynamic_segments[i][0..shelfSize(i)]);
            }
        }

        pub const Iterator = BaseIterator(*Self, *T);
        pub const ConstIterator = BaseIterator(*const Self, *const T);
        fn BaseIterator(comptime SelfType: type, comptime ElementPtr: type) type {
            return struct {
                list: SelfType,
                index: usize,
                box_index: usize,
                shelf_index: ShelfIndex,
                shelf_size: usize,

                pub fn next(it: *@This()) ?ElementPtr {
                    if (it.index >= it.list.len) return null;
                    if (it.index < prealloc_item_count) {
                        const ptr = &it.list.prealloc_segment[it.index];
                        it.index += 1;
                        if (it.index == prealloc_item_count) {
                            it.box_index = 0;
                            it.shelf_index = 0;
                            it.shelf_size = prealloc_item_count * 2;
                        }
                        return ptr;
                    }

                    const ptr = &it.list.dynamic_segments[it.shelf_index][it.box_index];
                    it.index += 1;
                    it.box_index += 1;
                    if (it.box_index == it.shelf_size) {
                        it.shelf_index += 1;
                        it.box_index = 0;
                        it.shelf_size *= 2;
                    }
                    return ptr;
                }

                pub fn prev(it: *@This()) ?ElementPtr {
                    if (it.index == 0) return null;

                    it.index -= 1;
                    if (it.index < prealloc_item_count) return &it.list.prealloc_segment[it.index];

                    if (it.box_index == 0) {
                        it.shelf_index -= 1;
                        it.shelf_size /= 2;
                        it.box_index = it.shelf_size - 1;
                    } else {
                        it.box_index -= 1;
                    }

                    return &it.list.dynamic_segments[it.shelf_index][it.box_index];
                }

                pub fn peek(it: *@This()) ?ElementPtr {
                    if (it.index >= it.list.len)
                        return null;
                    if (it.index < prealloc_item_count)
                        return &it.list.prealloc_segment[it.index];

                    return &it.list.dynamic_segments[it.shelf_index][it.box_index];
                }

                pub fn set(it: *@This(), index: usize) void {
                    it.index = index;
                    if (index < prealloc_item_count) return;
                    it.shelf_index = shelfIndex(index);
                    it.box_index = boxIndex(index, it.shelf_index);
                    it.shelf_size = shelfSize(@as(usize, it.shelf_index));
                }
            };
        }

        pub fn iterator(self: *Self, start_index: usize) Iterator {
            var it = Iterator{
                .list = self,
                .index = 0,
                .shelf_index = 0,
                .box_index = 0,
                .shelf_size = 0,
            };
            it.set(start_index);
            return it;
        }

        pub fn constIterator(self: *const Self, start_index: usize) ConstIterator {
            var it = ConstIterator{
                .list = self,
                .index = 0,
                .shelf_index = 0,
                .box_index = 0,
                .shelf_size = 0,
            };
            it.set(start_index);
            return it;
        }
    };
}

test "growth, reads and shrink at the shelf boundaries" {
    const List = SegmentedList(u32, 0);
    var list: List = .{};
    defer list.deinit(testing.allocator);

    // A list of `n` boxes owns `ceil(log2(n + 1))` shelves: no box at all fits
    // in no shelf, one box needs the size-1 shelf, and each further shelf
    // doubles the capacity.
    const shelf_counts = [_]usize{ 0, 1, 2, 2, 3, 3, 3, 3, 4, 4 };
    for (shelf_counts, 0..) |expected, capacity| {
        try list.setCapacity(testing.allocator, capacity);
        try testing.expectEqual(expected, list.dynamic_segments.len);
    }

    for (0..17) |i| {
        try list.append(testing.allocator, @intCast(i));
        try testing.expectEqual(i + 1, list.count());
    }
    for (0..17) |i| {
        try testing.expectEqual(@as(u32, @intCast(i)), list.at(i).*);
    }

    // Boxes that straddle a shelf boundary live in different shelves: 7 is the
    // last box of the size-4 shelf and 8 the first box of the size-8 shelf.
    try testing.expectEqual(@as(u32, 7), list.at(7).*);
    try testing.expectEqual(@as(u32, 8), list.at(8).*);

    var dest: [17]u32 = undefined;
    list.writeToSlice(&dest, 0);
    for (dest, 0..) |item, i| {
        try testing.expectEqual(@as(u32, @intCast(i)), item);
    }

    try testing.expectEqual(@as(u32, 16), list.pop().?);
    try testing.expectEqual(@as(usize, 16), list.count());

    // Shrinking drops the shelves above the requested capacity, down to none
    // at all, and the boxes that remain are still readable.
    list.shrink(8);
    list.shrinkCapacity(testing.allocator, 8);
    try testing.expectEqual(@as(usize, 4), list.dynamic_segments.len);
    for (0..8) |i| {
        try testing.expectEqual(@as(u32, @intCast(i)), list.at(i).*);
    }

    list.shrink(0);
    list.shrinkCapacity(testing.allocator, 0);
    try testing.expectEqual(@as(usize, 0), list.dynamic_segments.len);

    // The released shelves are allocated again on the next growth.
    for (0..9) |i| {
        try list.append(testing.allocator, @intCast(i));
    }
    for (0..9) |i| {
        try testing.expectEqual(@as(u32, @intCast(i)), list.at(i).*);
    }
    try testing.expectEqual(@as(usize, 4), list.dynamic_segments.len);
}

test "boxes hand over from the preallocated segment to the shelves" {
    const List = SegmentedList(u32, 4);
    var list: List = .{};
    defer list.deinit(testing.allocator);

    // The preallocated segment holds the first four boxes without a shelf.
    for (0..4) |i| {
        try list.append(testing.allocator, @intCast(i));
    }
    try testing.expectEqual(@as(usize, 0), list.dynamic_segments.len);

    // Box 4 is the first box of the first shelf, which holds eight boxes; box
    // 12 is the first box of the second one, which holds sixteen.
    for (4..20) |i| {
        try list.append(testing.allocator, @intCast(i));
    }
    try testing.expectEqual(@as(usize, 2), list.dynamic_segments.len);
    for (0..20) |i| {
        try testing.expectEqual(@as(u32, @intCast(i)), list.at(i).*);
    }

    list.shrink(0);
    list.shrinkCapacity(testing.allocator, 0);
    try testing.expectEqual(@as(usize, 0), list.dynamic_segments.len);

    for (0..20) |i| {
        try list.append(testing.allocator, @intCast(i));
    }
    for (0..20) |i| {
        try testing.expectEqual(@as(u32, @intCast(i)), list.at(i).*);
    }
}

/// Fill `list` with `filled` boxes — enough to fill every shelf it owns — and
/// then append one more, which is the first box of a shelf the list does not
/// own yet, so growing for it allocates.
fn fillThenCrossAShelfBoundary(allocator: Allocator, list: anytype, filled: usize) !void {
    for (0..filled) |i| {
        try list.append(allocator, @intCast(i));
    }
    const shelf_count = list.dynamic_segments.len;

    // A growth that cannot be satisfied must leave the list exactly as it
    // was: the same boxes, the same count, no shelf freed and none leaked.
    list.append(allocator, @intCast(filled)) catch |err| {
        try testing.expectEqual(filled, list.count());
        try testing.expectEqual(shelf_count, list.dynamic_segments.len);
        for (0..filled) |i| {
            try testing.expectEqual(@as(u32, @intCast(i)), list.at(i).*);
        }
        return err;
    };
    try testing.expectEqual(filled + 1, list.count());
    try testing.expectEqual(@as(u32, @intCast(filled)), list.at(filled).*);
    // The box did cost a shelf, so a run that fails here fails a shelf
    // allocation rather than running out of memory somewhere harmless.
    try testing.expectEqual(shelf_count + 1, list.dynamic_segments.len);
}

fn appendAcrossAShelfBoundary(allocator: Allocator) !void {
    var list: SegmentedList(u32, 0) = .{};
    defer list.deinit(allocator);
    // Boxes 0, 1 and 2 fill the first two shelves; box 3 opens the third.
    try fillThenCrossAShelfBoundary(allocator, &list, 3);
}

fn appendAcrossAShelfBoundaryFromPrealloc(allocator: Allocator) !void {
    var list: SegmentedList(u32, 4) = .{};
    defer list.deinit(allocator);
    // The preallocated segment and the first shelf hold twelve boxes; box 12
    // opens the second shelf.
    try fillThenCrossAShelfBoundary(allocator, &list, 12);
}

test "a failed growth leaves the list unchanged" {
    try testing.checkAllAllocationFailures(testing.allocator, appendAcrossAShelfBoundary, .{});
}

test "a failed growth from the preallocated segment leaves the list unchanged" {
    try testing.checkAllAllocationFailures(testing.allocator, appendAcrossAShelfBoundaryFromPrealloc, .{});
}
