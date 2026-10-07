//! Check signed negation before checking the destination integer range.
const std = @import("std");
const Ast = std.zig.Ast;
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const testing = @import("../../testing.zig");
const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const R = "intcast-of-negated-signed";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .intcast_of_negated_signed)) return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "@intCast")) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        if (params.len != 1) continue;
        const negative = negation(tree, params[0]) orelse continue;
        const operand = tree.nodeData(negative).node;
        const source = cache.intInfoOf(operand);
        if (source) |integer| {
            if (!integer.signed) continue;
        }
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!isRuntimeUse(tree, declaration, token)) continue;
        const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, negative, token, cache);
        const negation_fits = if (source) |integer|
            bounds.fitsInteger(integer.bits, true)
        else
            cache.comptimeIntValueOf(operand) != null;
        if (negation_fits) {
            if (cache.coercedIntInfoOf(node) orelse cache.intInfoOf(node)) |destination| {
                if (bounds.fitsInteger(destination.bits, destination.signed)) continue;
            }
        }
        const message = try gpa.dupe(u8, "the negation and destination conversion were not both proved in range; negating the signed minimum overflows even under a negative-sign guard; use @abs for an unsigned magnitude and separately check any narrower destination");
        errdefer gpa.free(message);
        try problems.append(gpa, .{
            .rule_id = R,
            .severity = .warning,
            .start = try Pos.fromTokenStart(tree, token),
            .end = try Pos.fromTokenEnd(tree, tree.lastToken(node)),
            .message = message,
        });
    }
}

/// True when the use at `token` runs at runtime: it sits inside
/// `declaration`'s body but outside any `comptime { … }` block (or
/// `comptime label: { … }` block) and outside the expression a bare
/// `comptime` keyword governs.  The compiler checks what it evaluates
/// itself, so a conversion that can only ever run there is not a
/// runtime hazard this rule reports.  A use this cannot place is a
/// runtime use: an unreadable seam declines into the check, never out
/// of it.
fn isRuntimeUse(tree: *const Ast, declaration: Ast.Node.Index, token: Ast.TokenIndex) bool {
    const body = tokens.bodyOf(tree, declaration) orelse return true;
    const first = tree.firstToken(body);
    if (token < first) return true;
    const tags = tree.tokens.items(.tag);
    var stack: [64]Ast.TokenIndex = undefined;
    var depth: usize = 0;
    var t = first;
    while (t <= token) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (depth < stack.len) stack[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
            },
            else => {},
        }
    }
    var i = depth;
    while (i > 0) {
        i -= 1;
        if (i >= stack.len) continue;
        const brace = stack[i];
        if (brace == 0) continue;
        if (tags[brace - 1] == .keyword_comptime) return false;
        if (brace >= 3 and tags[brace - 3] == .keyword_comptime and
            tags[brace - 2] == .identifier and tags[brace - 1] == .colon) return false;
    }
    return !statementStartsWithComptime(tags, first, token);
}

/// True when the statement owning `token` is written under a bare
/// `comptime` keyword (`comptime assert(x[i] == 0);`), or `token` sits
/// inside the parenthesised call such a keyword governs.  Only the
/// expression the keyword opens counts: once a group it did not open
/// closes, the rest of the statement runs at runtime.
fn statementStartsWithComptime(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, token: Ast.TokenIndex) bool {
    var start = first;
    var t = token;
    while (t > first) : (t -= 1) {
        switch (tags[t]) {
            .semicolon, .l_brace, .r_brace => {
                start = t + 1;
                break;
            },
            else => {},
        }
    }
    var c: ?Ast.TokenIndex = null;
    t = start;
    while (t < token) : (t += 1) {
        if (tags[t] == .keyword_comptime) {
            c = t;
            break;
        }
    }
    const comptime_tok = c orelse return false;
    var depth: i32 = 0;
    t = comptime_tok + 1;
    while (t < token) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => {
                depth -= 1;
                if (depth < 0) return false;
            },
            else => {},
        }
    }
    return true;
}

fn negation(tree: *const Ast, original: Ast.Node.Index) ?Ast.Node.Index {
    var node = original;
    for (0..64) |_| {
        if (tree.nodeTag(node) == .negation) return node;
        if (tree.nodeTag(node) != .grouped_expression) return null;
        node = tree.nodeData(node).node_and_token[0];
    }
    return null;
}

test "intcast-of-negated-signed: range proof retains minimum in the negative branch" {
    try testing.expectFiresTyped(check, R,
        \\fn magnitude(value: i32) u32 {
        \\    if (value < 0) return @intCast(-value);
        \\    return @intCast(value);
        \\}
    );
}

test "intcast-of-negated-signed: range proof excludes the signed minimum" {
    try testing.expectNoFireTyped(check,
        \\fn negate(value: i8) i8 {
        \\    if (value == -128) return 0;
        \\    return @intCast(-value);
        \\}
    );
}

test "intcast-of-negated-signed: the destination must also fit" {
    try testing.expectFiresTyped(check, R,
        \\fn magnitude(value: i32) u8 {
        \\    if (value < -1000 or value > 0) return 0;
        \\    return @intCast(-value);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn magnitude(value: i32) u8 {
        \\    if (value < -255 or value > 0) return 0;
        \\    return @intCast(-value);
        \\}
    );
}

test "intcast-of-negated-signed: unsigned magnitude and constant negation are safe" {
    try testing.expectNoFireTyped(check,
        \\fn magnitude(value: i64) u64 { return @abs(value); }
        \\fn constant() i32 { return @intCast(-1); }
    );
}

test "intcast-of-negated-signed: a format domain a switch arms over proves the negated exponent" {
    // What proves `-shift` here is the format domain — the union of the
    // two switches' arms — and not the `>= 0` test, which lets the
    // signed minimum through.  The exponent has to end up two-sided
    // before the branch narrows it, so both switches are read.
    try testing.expectNoFireTyped(check,
        \\const Format = enum { half, single, double };
        \\
        \\fn magnitude(format: Format, bits: u64) u64 {
        \\    const bias: i32 = switch (format) {
        \\        .half => 15,
        \\        .single => 127,
        \\        .double => 1023,
        \\    };
        \\    const fraction_bits: u6 = switch (format) {
        \\        .half => 10,
        \\        .single => 23,
        \\        .double => 52,
        \\    };
        \\    const raw = @as(i32, @intCast((bits >> fraction_bits) & 0x7ff));
        \\    const shift = raw - bias;
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: a domain that admits the signed minimum still reports" {
    // The same switch, reading its arms and then narrowing to the half
    // that negates: quiet only while no arm is the signed minimum.
    try testing.expectNoFireTyped(check,
        \\const Format = enum { half, reserved, double };
        \\
        \\fn magnitude(format: Format) u64 {
        \\    const shift: i32 = switch (format) {
        \\        .half => -15,
        \\        .reserved => -1023,
        \\        .double => -127,
        \\    };
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
    // One arm reaching `-2147483648` puts it back in the range the
    // negation reads, and no sign test excludes it there.
    try testing.expectFiresTyped(check, R,
        \\const Format = enum { half, reserved, double };
        \\
        \\fn magnitude(format: Format) u64 {
        \\    const shift: i32 = switch (format) {
        \\        .half => -15,
        \\        .reserved => -2147483648,
        \\        .double => -127,
        \\    };
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: an arm the oracle cannot bound keeps reporting" {
    try testing.expectNoFireTyped(check,
        \\const Format = enum { half, single, double };
        \\
        \\fn magnitude(format: Format) u64 {
        \\    const shift: i32 = switch (format) {
        \\        .half => -15,
        \\        .single => -127,
        \\        .double => -1023,
        \\    };
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
    // `spec.bias` is a field nothing in the range walk can bound, so
    // reading only the two literal arms would answer for a domain that
    // is really as wide as the declared type.
    try testing.expectFiresTyped(check, R,
        \\const Format = enum { half, single, double };
        \\const Spec = struct { bias: i32 };
        \\
        \\fn magnitude(format: Format, spec: *const Spec) u64 {
        \\    const shift: i32 = switch (format) {
        \\        .half => -15,
        \\        .single => spec.bias,
        \\        .double => -1023,
        \\    };
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: an unconstrained signed parameter keeps reporting" {
    // #78's limit: the proof comes from the operand's own domain, so a
    // generic helper handed a bare `i32` still reports.
    try testing.expectFiresTyped(check, R,
        \\fn magnitude(value: i32) u64 {
        \\    if (value >= 0) return @as(u64, @intCast(value));
        \\    return @as(u64, @intCast(-value));
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn magnitude(value: i32) u64 {
        \\    if (value == -2147483648) return 0;
        \\    if (value >= 0) return @as(u64, @intCast(value));
        \\    return @as(u64, @intCast(-value));
        \\}
    );
}

// ── The same format domain, one call boundary away ─────────────────────────
//
// The proof above is the two ends of one call: the DECODER is what bounds the
// exponent, and the MAGNITUDE is what negates it.  Reading the call through
// the type the decoder declared would answer `i32` — the widest value the
// declaration admits and none the body produces — and the negation would be
// back to the signed minimum.  What crosses the boundary is the range of
// every value the decoder can return, joined over its exits — where an exit
// the walk has to read before its own operand ran crosses as nothing, since
// that state is not the one the returned value comes from.

test "intcast-of-negated-signed: a callee's own return domain reaches its caller" {
    // The negation is proved from the operand's real range: the decoder
    // accepts three formats, so its result never reaches the signed minimum.
    // The `>= 0` test is what removes the positive half, and neither half of
    // the proof is the other one's job.
    try testing.expectNoFireTyped(check,
        \\const Format = enum { half, single, double };
        \\
        \\fn decodeExponent(format: Format, bits: u64) i32 {
        \\    const bias: i32 = switch (format) {
        \\        .half => 15,
        \\        .single => 127,
        \\        .double => 1023,
        \\    };
        \\    const fraction_bits: u6 = switch (format) {
        \\        .half => 10,
        \\        .single => 23,
        \\        .double => 52,
        \\    };
        \\    const raw = @as(i32, @intCast((bits >> fraction_bits) & 0x7ff));
        \\    return raw - bias;
        \\}
        \\
        \\fn magnitude(format: Format, bits: u64) u64 {
        \\    const shift = decodeExponent(format, bits);
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: a return domain that admits the signed minimum still reports" {
    // The same call boundary, with one arm that can hand back the signed
    // minimum.  A sign test cannot remove it, because it is on the negative
    // side, so the arm has to be stopped somewhere else.  What stops it is
    // that the switch this exit returns is no domain at all: the walk reads
    // an exit against the state from BEFORE its operand ran, and an operand
    // that runs code leaves a different state behind it.  The arms are never
    // joined, so the one reaching the minimum is in no claim either.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Format = enum { half, reserved, double };
        \\
        \\fn decodeExponent(format: Format, bits: u64) i32 {
        \\    const raw = @as(i32, @intCast((bits >> 10) & 0x7ff));
        \\    return switch (format) {
        \\        .half => raw - 15,
        \\        .reserved => std.math.minInt(i32),
        \\        .double => raw - 1023,
        \\    };
        \\}
        \\
        \\fn magnitude(format: Format, bits: u64) u64 {
        \\    const shift = decodeExponent(format, bits);
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: a callee that schedules a defer exports nothing" {
    // The deferred call runs at scope exit, where the walk of the body stops,
    // so a bound read off the body would describe a state the defer can still
    // invalidate.  The weaker answer is "unproven".
    try testing.expectFiresTyped(check, R,
        \\const Format = enum { half, single, double };
        \\
        \\fn trace() void {}
        \\
        \\fn decodeExponent(format: Format, bits: u64) i32 {
        \\    defer trace();
        \\    const raw = @as(i32, @intCast((bits >> 10) & 0x7ff));
        \\    return raw - 15;
        \\}
        \\
        \\fn magnitude(format: Format, bits: u64) u64 {
        \\    _ = format;
        \\    const shift = decodeExponent(format, bits);
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: an exit the walk cannot read exports nothing" {
    // Two exits, and the walk reads only one of them: `readBias` is a CALL,
    // which is not an expression it can evaluate, so that exit is withdrawn
    // and the summary is dropped rather than narrowed by the exit it did
    // read.  What the callee really returns there is a bare `i32` field, so
    // the signed minimum is among its values and the caller's `-shift`
    // overflows on that path — the consumer is unsafe on its own account,
    // not because of what the readable exit happens to say.
    //
    // The shape this replaces returned `raw - spec.bias` and reached the
    // signed minimum only by way of how the difference is bounded: `raw` is
    // `(bits >> 10) & 0x7ff`, so `raw - bias` spans
    // [-2147483647, 2147485695], and whether that leaves `i32` — and so
    // whether the minimum is in the exported domain — is a property of the
    // arithmetic, not of the source.  Asking this rule to report on that
    // would have pinned the bound, not the exit.
    try testing.expectFiresTyped(check, R,
        \\const Format = enum { half, single, double };
        \\const Spec = struct { raw_bits: u64, bias: i32 };
        \\
        \\fn readBias(spec: *const Spec) i32 { return spec.bias; }
        \\
        \\fn decodeExponent(format: Format, spec: *const Spec) i32 {
        \\    if (spec.raw_bits == 0) return readBias(spec);
        \\    const raw = @as(i32, @intCast((spec.raw_bits >> 10) & 0x7ff));
        \\    return raw - 15;
        \\}
        \\
        \\fn magnitude(format: Format, spec: *const Spec) u64 {
        \\    _ = format;
        \\    const shift = decodeExponent(format, spec);
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: a caller-local of the same spelling is not a callee exit" {
    // The exits are read in the CALLEE's scope, where `bias` is the format
    // domain.  A local of the caller spelled the same holds a different
    // value; reading it as one of the callee's returns would put the signed
    // minimum back into a domain that does not contain it.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Format = enum { half, single, double };
        \\
        \\fn decodeExponent(format: Format, bits: u64) i32 {
        \\    const bias: i32 = switch (format) {
        \\        .half => 15,
        \\        .single => 127,
        \\        .double => 1023,
        \\    };
        \\    const raw = @as(i32, @intCast((bits >> 10) & 0x7ff));
        \\    return raw - bias;
        \\}
        \\
        \\fn magnitude(format: Format, bits: u64) u64 {
        \\    const bias: i32 = std.math.minInt(i32);
        \\    _ = bias;
        \\    const shift = decodeExponent(format, bits);
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: a return that runs its own operand exports nothing" {
    // The walk reads a `return` where the statement stands, which is the
    // state from BEFORE the operand ran.  `zeroThen` rewrites `shift` inside
    // that operand, so both arms are read at -1 and the exit joins into a
    // body that can only ever hand back -1.  It hands back the signed
    // minimum instead, and the caller's negation is what overflows there.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn zeroThen(p: *i32) bool {
        \\    p.* = std.math.minInt(i32);
        \\    return true;
        \\}
        \\
        \\fn decode() i32 {
        \\    var shift: i32 = -1;
        \\    return switch (zeroThen(&shift)) {
        \\        false => shift,
        \\        true => shift,
        \\    };
        \\}
        \\
        \\fn magnitude() u64 {
        \\    const shift = decode();
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
    // The control: the same call boundary and the same consumer, with a
    // decoder whose return operand runs no code.  Nothing moves between the
    // state the exit is read at and the value it produces, so the domain the
    // body really returns is still what crosses, and the negation is proved
    // from it rather than from the declared `i32`.
    try testing.expectNoFireTyped(check,
        \\fn decodeExponent(bits: u64) i32 {
        \\    const raw = @as(i32, @intCast((bits >> 10) & 0x7ff));
        \\    return raw - 15;
        \\}
        \\
        \\fn magnitude(bits: u64) u64 {
        \\    const shift = decodeExponent(bits);
        \\    if (shift >= 0) return @as(u64, @intCast(shift));
        \\    return @as(u64, @intCast(-shift));
        \\}
    );
}

test "intcast-of-negated-signed: a closed helper excludes minimum only through all callers" {
    try testing.expectNoFireTyped(check,
        \\fn magnitude(offset: isize) usize {
        \\    if (offset >= 0) return @intCast(offset);
        \\    return @intCast(-offset);
        \\}
        \\pub fn use(index: u16) usize {
        \\    return magnitude(-@as(isize, @intCast(index)));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn magnitude(offset: isize) usize {
        \\    if (offset >= 0) return @intCast(offset);
        \\    return @intCast(-offset);
        \\}
        \\pub fn use(index: u16, offset: isize) usize {
        \\    return magnitude(-@as(isize, @intCast(index))) + magnitude(offset);
        \\}
    );
}

test "intcast-of-negated-signed: closed i24 and u32 callers bound scaled negation" {
    // Joining both callers gives [-8388608, 4294967295]. Scaling by four
    // stays in i64; the negative branch's magnitude is at most 33554432.
    try testing.expectNoFireTyped(check,
        \\const Inst = packed struct(u32) { payload: u32 };
        \\fn magnitude(offset: i64) usize {
        \\    const delta = offset * @as(i64, @intCast(@sizeOf(Inst)));
        \\    if (delta < 0) return @intCast(-delta);
        \\    return @intCast(delta);
        \\}
        \\pub fn narrow(value: i24) usize { return magnitude(value); }
        \\pub fn extension(value: u32) usize { return magnitude(@intCast(value)); }
    );
}

test "intcast-of-negated-signed: a scaled signed minimum caller retains the warning" {
    try testing.expectFiresTyped(check, R,
        \\const Inst = packed struct(u32) { payload: u32 };
        \\fn magnitude(offset: i64) usize {
        \\    const delta = offset * @as(i64, @intCast(@sizeOf(Inst)));
        \\    if (delta < 0) return @intCast(-delta);
        \\    return @intCast(delta);
        \\}
        \\pub fn narrow(value: i24) usize { return magnitude(value); }
        \\pub fn extension(value: u32) usize { return magnitude(@intCast(value)); }
        \\pub fn minimum() usize { return magnitude(-2305843009213693952); }
    );
}

test "intcast-of-negated-signed: public scaled helpers have an open caller domain" {
    try testing.expectFiresTyped(check, R,
        \\const Inst = packed struct(u32) { payload: u32 };
        \\pub fn magnitude(offset: i64) usize {
        \\    const delta = offset * @as(i64, @intCast(@sizeOf(Inst)));
        \\    if (delta < 0) return @intCast(-delta);
        \\    return @intCast(delta);
        \\}
        \\pub fn narrow(value: i24) usize { return magnitude(value); }
        \\pub fn extension(value: u32) usize { return magnitude(@intCast(value)); }
    );
}

test "intcast-of-negated-signed: escaped scaled helpers have an open caller domain" {
    try testing.expectFiresTyped(check, R,
        \\const Inst = packed struct(u32) { payload: u32 };
        \\fn magnitude(offset: i64) usize {
        \\    const delta = offset * @as(i64, @intCast(@sizeOf(Inst)));
        \\    if (delta < 0) return @intCast(-delta);
        \\    return @intCast(delta);
        \\}
        \\pub fn narrow(value: i24) usize { return magnitude(value); }
        \\pub fn extension(value: u32) usize { return magnitude(@intCast(value)); }
        \\pub fn callback() *const fn (i64) usize { return &magnitude; }
    );
}

test "intcast-of-negated-signed: an opaque caller argument prevents a scaled proof" {
    try testing.expectFiresTyped(check, R,
        \\const Inst = packed struct(u32) { payload: u32 };
        \\extern fn readOffset() i64;
        \\fn magnitude(offset: i64) usize {
        \\    const delta = offset * @as(i64, @intCast(@sizeOf(Inst)));
        \\    if (delta < 0) return @intCast(-delta);
        \\    return @intCast(delta);
        \\}
        \\pub fn narrow(value: i24) usize { return magnitude(value); }
        \\pub fn extension(value: u32) usize { return magnitude(@intCast(value)); }
        \\pub fn opaqueValue() usize { return magnitude(readOffset()); }
    );
}

test "intcast-of-negated-signed: a private sign-extended immediate excludes minimum" {
    try testing.expectNoFireTyped(check,
        \\fn signExtend(comptime bits: u6, value: u32) i32 {
        \\    const shift: u5 = @intCast(32 - bits);
        \\    return @as(i32, @bitCast(value << shift)) >> shift;
        \\}
        \\fn immediateI(word: u32) i32 { return signExtend(12, word >> 20); }
        \\pub fn frameSize(word: u32) ?u32 {
        \\    const immediate = immediateI(word);
        \\    if (immediate < 0) return @intCast(-immediate);
        \\    return null;
        \\}
    );
}

test "intcast-of-negated-signed: a full-width signed immediate retains minimum" {
    try testing.expectFiresTyped(check, R,
        \\fn signExtend(comptime bits: u6, value: u32) i32 {
        \\    const shift: u5 = @intCast(32 - bits);
        \\    return @as(i32, @bitCast(value << shift)) >> shift;
        \\}
        \\fn immediateI(word: u32) i32 { return signExtend(32, word); }
        \\pub fn frameSize(word: u32) ?u32 {
        \\    const immediate = immediateI(word);
        \\    if (immediate < 0) return @intCast(-immediate);
        \\    return null;
        \\}
    );
}

test "intcast-of-negated-signed: an unbound immediate width stays conservative" {
    try testing.expectFiresTyped(check, R,
        \\fn signExtend(comptime bits: u6, value: u32) i32 {
        \\    const shift: u5 = @intCast(32 - bits);
        \\    return @as(i32, @bitCast(value << shift)) >> shift;
        \\}
        \\pub fn frameSize(comptime bits: u6, word: u32) ?u32 {
        \\    const immediate = signExtend(bits, word);
        \\    if (immediate < 0) return @intCast(-immediate);
        \\    return null;
        \\}
    );
}

test "intcast-of-negated-signed: a forwarded call cannot read arguments before their effects" {
    try testing.expectFiresTyped(check, R,
        \\fn reset(value: *i32) i32 {
        \\    value.* = -2147483648;
        \\    return 0;
        \\}
        \\fn second(first: i32, value: i32) i32 { _ = first; return value; }
        \\fn immediateI() i32 {
        \\    var value: i32 = -1;
        \\    return second(reset(&value), value);
        \\}
        \\pub fn frameSize() ?u32 {
        \\    const immediate = immediateI();
        \\    if (immediate < 0) return @intCast(-immediate);
        \\    return null;
        \\}
    );
}
