// memset-undef-after-len-truncation — ziglang/zig#25810 + #25832.
// `self.items.len = NEW; @memset(self.items[NEW..], undefined);`
// memsets an empty slice → no-op → defeats undefined poisoning.

const std = @import("std");

const ShrinkableList = struct {
    items: []u8,

    // Bug — `len` truncated BEFORE memset.  Fires on @memset.
    pub fn shrinkBuggy(self: *ShrinkableList, new_len: usize) void {
        if (new_len >= self.items.len) return;
        self.items.len = new_len;
        @memset(self.items[new_len..], undefined);
    }

    // Bug — clear variant.
    pub fn clearBuggy(self: *ShrinkableList) void {
        if (self.items.len == 0) return;
        self.items.len = 0;
        @memset(self.items, undefined);
    }

    // Control — memset BEFORE truncation.  Should NOT fire.
    pub fn shrinkFixed(self: *ShrinkableList, new_len: usize) void {
        @memset(self.items[new_len..], undefined);
        self.items.len = new_len;
    }

    pub fn clearFixed(self: *ShrinkableList) void {
        @memset(self.items, undefined);
        self.items.len = 0;
    }
};
