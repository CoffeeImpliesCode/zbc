//! Detects slicing from a non-zero constant offset into a slice/array whose
//! length is not checked before the slice expression:
//!
//!   const tail = line[6..];   // BUG: crashes / OOB if line.len < 6
//!
//! In Zig, `buf[N..]` where `buf.len < N` is a safety-checked out-of-bounds
//! error (trapping in Debug/ReleaseSafe, undefined behaviour in ReleaseFast).
//! When `buf` comes from user or network input the length is unconstrained.
//!
//! Fix: check `buf.len` before slicing:
//!   if (buf.len < 6) return error.TruncatedInput;
//!   const tail = buf[6..];
//!
//! Real-world shape: oven-sh/bun#31227 (patch/lib.rs Zig-mirror pattern —
//! `line[b"--- a/".len()..] ` panics on a truncated `--- a/` header line),
//! oven-sh/bun#31264 (eql_case_insensitive_ascii OOB when input shorter than
//! the keyword literal).
//!
//! Detection (Tier 1, per-fn body token walk):
//!   1. Scan for `identifier l_bracket number_literal(N) ellipsis2 r_bracket`
//!      where N > 0 (i.e., `buf[N..]`).
//!   2. The number_literal must represent a value > 0 (skip `buf[0..]`).
//!   3. Suppression: if `identifier(buf) period identifier(len)` appears
//!      anywhere in the fn body before the slice token, the programmer is
//!      already consulting `.len` on that buffer — do not fire.
//!   4. Suppression: if the preceding token before `identifier(buf)` is
//!      `period` (chain: `self.buf[N..]`) — the receiver has more context;
//!      skip to reduce noise on deeply-chained field accesses.
//!   5. Suppression: self-advance / consume idiom `buf = buf[N..]` (the slice
//!      is a reassignment of the buffer to a sub-slice of itself). This is the
//!      iterate/consume shape — guarded in practice by a `buf[0]` access, a
//!      loop length guard, or a `startsWith` check — and is categorically
//!      distinct from the "parse a fixed prefix from input" bug this rule
//!      targets (`const tail = line[6..]`). Suppressing it preserves recall on
//!      the real bug shape while removing the dominant FP class.
//!   6. Suppression: a length lower-bound proven before the slice.  An index
//!      `buf[K]` proves `len >= K+1`; a closed-end slice `buf[A..M]` proves
//!      `len >= M`.  When the strongest bound is >= the offset, the slice is
//!      in-bounds (e.g. `buf[0..4].* = …; buf[4..]`).
//!   7. Suppression: a prefix-check guard `startsWith*/hasPrefix*(…, buf,
//!      "literal")` before the slice proves `buf.len >= literal.len`; when that
//!      byte length is >= the offset, `buf[offset..]` is in-bounds.
//!   8. Suppression: `buf` is a local fixed-size array (`var buf: [K]T` or
//!      `var buf = [_]T{…}`).  Array slicing is compile-time bounds checked,
//!      so a `buf[N..]` that compiles is always in-bounds — it can never be the
//!      runtime OOB this rule targets (a `[]T` slice of unconstrained length).
//!   9. Suppression (cross-fn, 1-hop): `const buf = CALLEE(…); buf[N..]` where
//!      CALLEE's inferred return-length postcondition is >= N.  The postcondition
//!      is inferred from CALLEE's body (all returns are bounded string literals,
//!      directly or via a `return switch {…}`).  See `FileCtx`.
//!  10. Suppression (cross-fn, 2-hop): `buf` is parameter `i` of a private free
//!      fn and every in-file caller passes an argument of provable length >= N
//!      at position `i` — a string literal, or a call whose callee's
//!      return-length postcondition is >= N (e.g. `close_tag[2..]` where callers
//!      pass `chunk.closingTagForContent()` → returns `"</script"`/`"</style"`).
//!  11. Suppression: `buf` is a `comptime` parameter.  Zig comptime-evaluates
//!      every instantiation site, so `buf[N..]` that compiles is always
//!      in-bounds — the compiler would reject a caller passing a too-short
//!      literal before the function body ever executes.
//!  12. Fire at the `l_bracket` token of the unsafe slice.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const value_range = @import("../../flow/value_range.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "slice-from-fixed-offset-without-len-check";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .slice_from_fixed_offset_without_len_check)) return;

    var ctx = try FileCtx.build(gpa, tree);
    defer ctx.deinit(gpa);

    // Map each slice expression's `[` token → its operand AST node, so the
    // token-walk firing site (keyed on the l_bracket token) can recover the
    // operand node and ask the type engine for its fixed-array length.  Built
    // once per file; empty/unused when the type resolver is absent.
    var slice_ops: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty;
    defer slice_ops.deinit(gpa);
    {
        var ni: u32 = 0;
        while (ni < tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            switch (tree.nodeTag(node)) {
                .slice_open, .slice, .slice_sentinel => {
                    const sl = tree.fullSlice(node) orelse continue;
                    try slice_ops.put(gpa, tree.nodeMainToken(node), sl.ast.sliced);
                },
                else => {},
            }
        }
    }

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try checkBody(gpa, tree, cache, &ctx, &slice_ops, fn_entry.name_token, fn_entry.proto, fn_entry.body, problems);
    }
}

/// Cross-fn analysis tracks at most this many leading parameters per function.
const MAX_PARAMS = 8;

/// Per-parameter minimum caller-argument length for a free private fn.
/// `min[i]` = the smallest provable length passed at position `i` across all
/// in-file call sites; `maxInt` means "no call site observed for that position"
/// (so no conclusion).  `0` means a caller passed an unbounded argument.
const ParamBounds = struct {
    min: [MAX_PARAMS]usize = @splat(std.math.maxInt(usize)),
};

/// File-level cross-fn context, built once per source file.  String keys are
/// token slices, stable for the lifetime of the Ast.
const FileCtx = struct {
    /// fn name → a conservative lower bound on the length of *every* value the
    /// function returns.  Present only when all returns are bounded string
    /// literals (a direct `return "lit"` or a `return switch {…}` whose arms are
    /// all string literals / diverging).  A name with even one unbounded return
    /// is absent (poisoned), so a `const x = f(); x[N..]` may be suppressed iff
    /// `return_minlen[f] >= N`.
    return_minlen: std.StringHashMapUnmanaged(usize),

    /// free-fn name → per-parameter min caller-argument length.  Populated only
    /// for **private** (non-`pub`) **free** functions (no `self`/`this`
    /// receiver) whose name is unique in the file, so the in-file call sites are
    /// the exhaustive caller set.  Lets a param slice `p[N..]` be suppressed when
    /// every caller passes an argument of provable length >= N at p's position.
    param_minlen: std.StringHashMapUnmanaged(ParamBounds),

    fn build(gpa: std.mem.Allocator, tree: *const Ast) !FileCtx {
        var ctx: FileCtx = .{ .return_minlen = .empty, .param_minlen = .empty };
        errdefer ctx.deinit(gpa);
        try ctx.fillReturnMinLen(gpa, tree);
        try ctx.fillParamMinLen(gpa, tree);
        return ctx;
    }

    fn deinit(self: *FileCtx, gpa: std.mem.Allocator) void {
        self.return_minlen.deinit(gpa);
        self.param_minlen.deinit(gpa);
    }

    /// Infer each fn's return-length postcondition.  Names with any unbounded
    /// return are poisoned (removed) to stay sound under name collisions (e.g.
    /// two `foo` methods on different types).
    fn fillReturnMinLen(self: *FileCtx, gpa: std.mem.Allocator, tree: *const Ast) !void {
        const tags = tree.tokens.items(.tag);
        var poisoned: std.StringHashMapUnmanaged(void) = .empty;
        defer poisoned.deinit(gpa);

        var proto_buf: [1]Ast.Node.Index = undefined;
        var fns = tokens.iterFnDecls(tree);
        while (fns.next(&proto_buf)) |e| {
            const name = tree.tokenSlice(e.name_token);
            if (poisoned.contains(name)) continue;
            if (inferReturnMinLen(tree, tags, e.body)) |len| {
                const gop = try self.return_minlen.getOrPut(gpa, name);
                gop.value_ptr.* = if (gop.found_existing) @min(gop.value_ptr.*, len) else len;
            } else {
                try poisoned.put(gpa, name, {});
                _ = self.return_minlen.remove(name);
            }
        }
    }

    /// Build `param_minlen` for private free fns by inferring, from every
    /// in-file call site, the min argument length passed at each parameter
    /// position.  Depends on `return_minlen` (a call argument's length may come
    /// from the callee's return-length postcondition), so run it second.
    fn fillParamMinLen(self: *FileCtx, gpa: std.mem.Allocator, tree: *const Ast) !void {
        const tags = tree.tokens.items(.tag);

        // Pass A — candidate free private fns: name must be unique, non-`pub`,
        // and have no `self`/`this` receiver (so call args map directly to
        // params).  Names failing any of these (or appearing twice) are poisoned.
        var poisoned: std.StringHashMapUnmanaged(void) = .empty;
        defer poisoned.deinit(gpa);
        var proto_buf: [1]Ast.Node.Index = undefined;
        var fns = tokens.iterFnDecls(tree);
        while (fns.next(&proto_buf)) |e| {
            const name = tree.tokenSlice(e.name_token);
            if (poisoned.contains(name)) continue;

            const is_pub = e.proto.visib_token != null;
            const first = tokens.firstParamName(tree, e.proto);
            const is_method = first != null and
                (std.mem.eql(u8, first.?, "self") or std.mem.eql(u8, first.?, "this"));
            var nparams: u32 = 0;
            var it = e.proto.iterate(tree);
            while (it.next()) |_| nparams += 1;

            const disqualified = is_pub or is_method or nparams == 0 or nparams > MAX_PARAMS;
            if (disqualified or self.param_minlen.contains(name)) {
                try poisoned.put(gpa, name, {});
                _ = self.param_minlen.remove(name);
                continue;
            }
            try self.param_minlen.put(gpa, name, .{});
        }

        // Pass B — visit every call site `NAME(args)` of a candidate (excluding
        // the definition `fn NAME(`) and fold each argument's length into the
        // per-position minimum.  Counting extra/spurious call sites only lowers a
        // minimum, so it is conservative; missing a real caller would not be —
        // hence the uniqueness/visibility restrictions in Pass A.
        // The last token index is already a `TokenIndex` — a `u32` — so
        // the call-site scan bound needs no conversion of the token
        // count to re-narrow.  The scan reads `i` and `i + 1`.
        const last_tok = tree.lastToken(.root);
        var i: u32 = 0;
        while (i < last_tok) : (i += 1) {
            if (tags[i] != .identifier) continue;
            if (tags[i + 1] != .l_paren) continue;
            if (i > 0 and tags[i - 1] == .keyword_fn) continue; // definition, not a call
            const bounds = self.param_minlen.getPtr(tree.tokenSlice(i)) orelse continue;

            const lp = i + 1;
            var d: u32 = 0;
            var ai: u32 = 0;
            var astart: u32 = lp + 1;
            var k: u32 = lp;
            while (k <= last_tok) : (k += 1) {
                switch (tags[k]) {
                    .l_paren, .l_brace, .l_bracket => d += 1,
                    .r_brace, .r_bracket => d -= 1,
                    .r_paren => {
                        d -= 1;
                        if (d == 0) {
                            if (k > astart and ai < MAX_PARAMS) {
                                const al = argMinLen(tree, tags, astart, k, &self.return_minlen);
                                bounds.min[ai] = @min(bounds.min[ai], al);
                            }
                            break;
                        }
                    },
                    .comma => if (d == 1) {
                        if (ai < MAX_PARAMS) {
                            const al = argMinLen(tree, tags, astart, k, &self.return_minlen);
                            bounds.min[ai] = @min(bounds.min[ai], al);
                        }
                        ai += 1;
                        astart = k + 1;
                    },
                    else => {},
                }
            }
        }
    }
};

/// Conservative lower bound on the length of a single call-argument token range
/// `[start, end)`.  Recognises a pure string-literal argument (its byte length)
/// and a call argument `[try] …CALLEE(…)` (the callee's return-length
/// postcondition).  Everything else yields 0 (unknown).
fn argMinLen(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    return_minlen: *const std.StringHashMapUnmanaged(usize),
) usize {
    if (start >= end) return 0;
    var s = start;
    if (tags[s] == .keyword_try) s += 1;
    if (s >= end) return 0;

    // Pure string-literal argument.
    if (tags[s] == .string_literal and s + 1 == end) {
        return stringLiteralMinByteLen(tree.tokenSlice(s));
    }

    // Call argument: ends in `)`; callee is the identifier before its `(`.
    if (tags[end - 1] == .r_paren) { // zbc-disable-line: index-minus-one-without-zero-guard — end>s>=0 via `if (s >= end) return 0` above
        var d: u32 = 0;
        var k = end - 1;
        while (k > s) : (k -= 1) {
            if (tags[k] == .r_paren) {
                d += 1;
            } else if (tags[k] == .l_paren) {
                d -= 1;
                if (d == 0) break;
            }
        }
        if (tags[k] == .l_paren and k > s and tags[k - 1] == .identifier) {
            return return_minlen.get(tree.tokenSlice(k - 1)) orelse 0;
        }
    }
    return 0;
}

/// Conservative lower bound on the length of every value `body` returns, or
/// null if any return is not a bounded string literal.  Handles a direct
/// `return "lit"` and a `return switch (…) { arms }` whose arms are all string
/// literals or diverging (`unreachable` / `@panic` / `@compileError` / nested
/// `return`).  Anything else (a variable, a slice expr, an `if`-return) yields
/// null so the caller makes no unsound assumption.
fn inferReturnMinLen(tree: *const Ast, tags: []const std.zig.Token.Tag, body: Ast.Node.Index) ?usize {
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var best: usize = std.math.maxInt(usize);
    var saw_value = false;
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_return) continue;
        if (t + 1 > last) return null;
        const v = t + 1;
        switch (tags[v]) {
            .semicolon => {}, // `return;` — void, irrelevant to slice length
            .string_literal => {
                best = @min(best, stringLiteralMinByteLen(tree.tokenSlice(v)));
                saw_value = true;
            },
            .keyword_switch => {
                const sw = analyzeReturnSwitch(tree, tags, v, last) orelse return null;
                best = @min(best, sw);
                saw_value = true;
            },
            else => return null, // unbounded return → no guarantee
        }
    }
    if (!saw_value) return null;
    return best;
}

/// Lower bound on the value of a `return switch (…) { arms }` whose arms are all
/// string literals or diverging.  Returns the minimum literal byte length, or
/// null if any arm value cannot be bounded.
fn analyzeReturnSwitch(tree: *const Ast, tags: []const std.zig.Token.Tag, sw_tok: Ast.TokenIndex, last: Ast.TokenIndex) ?usize {
    var k: Ast.TokenIndex = sw_tok + 1;
    if (k > last or tags[k] != .l_paren) return null;
    // Skip the `( condition )`.
    var pd: u32 = 0;
    while (k <= last) : (k += 1) {
        if (tags[k] == .l_paren) {
            pd += 1;
        } else if (tags[k] == .r_paren) {
            pd -= 1;
            if (pd == 0) {
                k += 1;
                break;
            }
        }
    }
    if (k > last or tags[k] != .l_brace) return null;
    const brace_open = k;
    // Brace-match the switch body.
    var bd: u32 = 0;
    var end: Ast.TokenIndex = brace_open;
    {
        var j: Ast.TokenIndex = brace_open;
        while (j <= last) : (j += 1) {
            if (tags[j] == .l_brace) {
                bd += 1;
            } else if (tags[j] == .r_brace) {
                bd -= 1;
                if (bd == 0) {
                    end = j;
                    break;
                }
            }
        }
        if (bd != 0) return null;
    }
    // Scan each arm value (token after `=>` at brace depth 1).
    var best: usize = std.math.maxInt(usize);
    var saw = false;
    var d: u32 = 0;
    var i: Ast.TokenIndex = brace_open;
    while (i <= end) : (i += 1) {
        switch (tags[i]) {
            .l_brace, .l_paren, .l_bracket => d += 1,
            .r_brace, .r_paren, .r_bracket => d -= 1,
            .equal_angle_bracket_right => if (d == 1 and i + 1 <= end) {
                const v = i + 1;
                switch (tags[v]) {
                    .string_literal => {
                        best = @min(best, stringLiteralMinByteLen(tree.tokenSlice(v)));
                        saw = true;
                    },
                    .keyword_unreachable, .keyword_return => {}, // diverging arm
                    .builtin => {
                        const b = tree.tokenSlice(v);
                        if (!std.mem.eql(u8, b, "@panic") and !std.mem.eql(u8, b, "@compileError")) return null;
                    },
                    else => return null, // un-boundable arm value
                }
            },
            else => {},
        }
    }
    if (!saw) return null;
    return best;
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    ctx: *const FileCtx,
    slice_ops: *const std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),
    name_token: Ast.TokenIndex,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // If this fn is a cross-fn param candidate, gather its parameter names so a
    // param slice `p[N..]` can be matched to its caller-derived length bound.
    const param_bounds: ?ParamBounds = ctx.param_minlen.get(tree.tokenSlice(name_token));
    var param_names: [MAX_PARAMS][]const u8 = undefined;
    var nparams: u32 = 0;
    if (param_bounds != null) {
        var it = proto.iterate(tree);
        while (it.next()) |p| {
            if (nparams >= MAX_PARAMS) break;
            param_names[nparams] = if (p.name_token) |nt| tree.tokenSlice(nt) else "";
            nparams += 1;
        }
    }

    var t: Ast.TokenIndex = first;
    while (t + 3 <= last) : (t += 1) {
        // Skip nested fn bodies.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: `identifier l_bracket number_literal ellipsis2 r_bracket`
        //   t+0: identifier (the buffer/slice variable)
        //   t+1: l_bracket
        //   t+2: number_literal (the offset N)
        //   t+3: ellipsis2 (..)
        //   t+4: r_bracket  (we check t+4 <= last)
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_bracket) continue;
        if (tags[t + 2] != .number_literal) continue;
        if (tags[t + 3] != .ellipsis2) continue;
        if (t + 4 > last) continue;
        if (tags[t + 4] != .r_bracket) continue;

        const offset_str = tree.tokenSlice(t + 2);

        // Skip `buf[0..]` — always safe.
        if (std.mem.eql(u8, offset_str, "0")) continue;

        const buf_name = tree.tokenSlice(t);

        // Suppression: skip if the identifier is a chained field access
        // (`self.buf[N..]`). The receiver provides more context and static
        // analysis becomes very imprecise without type info (Tier 4).
        if (t > first and tags[t - 1] == .period) continue;

        // Suppression: self-advance / consume idiom `buf = buf[N..]` — the
        // slice reassigns the buffer to a sub-slice of itself. This is the
        // iterate/consume shape, not the fixed-prefix-parse shape this rule
        // targets. The `(t - 3) != period` guard avoids matching a field
        // assignment whose field happens to share the local's name
        // (`obj.buf = buf[N..]`).
        if (t >= first + 2 and
            tags[t - 1] == .equal and
            tags[t - 2] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t - 2), buf_name) and
            (t < first + 3 or tags[t - 3] != .period))
        {
            continue;
        }

        // Suppression: if `buf_name.len` appears in the fn body BEFORE
        // this slice, the programmer already consults the length.
        if (lenCheckedBefore(tree, tags, first, t, buf_name)) continue;

        // Suppression: a length lower-bound established before the slice.
        // An index access `buf[K]` proves `buf.len >= K+1`; a closed-end slice
        // `buf[A..M]` (M a literal) proves `buf.len >= M`.  When the strongest
        // such bound is >= the slice offset, `buf[offset..]` is in-bounds.
        // (Generalises the old `buf[0]`-for-offset-1 check to any offset.)
        if (offsetValue(offset_str)) |off| {
            if (provenMinLenBefore(tree, tags, first, t, buf_name) >= off) continue;
            // Consume the shared oracle's length guards and initializer
            // extents at this use. Runtime slice endpoints and checked return
            // lengths require the same branch and mutation proofs as numeric
            // indices; missing proof stays unsafe and query errors propagate.
            if (try value_range.provesMinLen(gpa, tree, body, buf_name, off, t, cache)) continue;
        }

        // Suppression: a prefix-check guard `startsWith*/hasPrefix*(…, buf,
        // "literal")` before the slice proves `buf.len >= literal.len`.  When
        // the prefix's byte length is >= the slice offset, `buf[offset..]` is
        // safe.
        if (prefixCheckGuardBefore(tree, tags, first, t, buf_name, offset_str)) continue;

        // Suppression: `buf` is a local fixed-size array (`var buf: [K]T` or
        // `var buf = [_]T{…}`).  A fixed-array slice is compile-time bounds
        // checked — if `buf[N..]` compiles then N <= K — so it can never be the
        // runtime out-of-bounds this rule targets (which is a `[]T` slice whose
        // length is unconstrained).  (Tier 3: local declaration tracking.)
        if (isLocalFixedArray(tree, tags, first, t, buf_name)) continue;

        // Suppression (type engine): the operand resolves to a fixed-size array
        // `[K]T` (or single-pointer `*[K]T`) with K >= offset.  Unlike the
        // token-based local-array check above, this also covers parameters,
        // struct fields, and call results whose type is a fixed array — the
        // length is a compiler-guaranteed constant, so `buf[offset..]` that
        // compiles is always in-bounds.  No-op when the resolver is absent.
        if (offsetValue(offset_str)) |off| {
            if (slice_ops.get(t + 1)) |operand_node| {
                if (cache.fixedArrayLenOf(operand_node)) |alen| {
                    if (alen >= off) continue;
                }
            }
        }

        // Suppression (cross-fn, 1-hop): `const buf = CALLEE(…); buf[N..]` where
        // CALLEE has a return-length postcondition >= N.  `CALLEE` returns slices
        // of provable min length (see `FileCtx.return_minlen`), so the slice is
        // in-bounds.
        if (offsetValue(offset_str)) |off| {
            if (localInitCallee(tree, tags, first, t, buf_name)) |callee| {
                if (ctx.return_minlen.get(callee)) |minlen| {
                    if (minlen >= off) continue;
                }
            }
        }

        // Suppression (cross-fn, 2-hop): `buf` is parameter `i` of this private
        // free fn, and every in-file caller passes an argument of provable length
        // >= N at position `i` (a string literal, or a call whose callee's
        // return-length postcondition is >= N).  See `FileCtx.param_minlen`.
        if (param_bounds) |pb| {
            if (offsetValue(offset_str)) |off| {
                var pi: u32 = 0;
                var suppressed = false;
                while (pi < nparams) : (pi += 1) {
                    if (!std.mem.eql(u8, param_names[pi], buf_name)) continue;
                    const m = pb.min[pi];
                    if (m != std.math.maxInt(usize) and m >= off) suppressed = true;
                    break;
                }
                if (suppressed) continue;
            }
        }

        // Suppression: `buf` is a `comptime` parameter.  Every instantiation
        // is compile-time evaluated — a too-short literal would be a compile
        // error at the call site, not a runtime OOB.
        if (isComptimeParam(proto, tree, tags, buf_name)) continue;

        // Fire at the l_bracket of the unsafe slice.
        try report(gpa, problems, tree, t + 1, buf_name, offset_str);
    }
}

/// Returns true iff `identifier(name) period identifier(len)` appears
/// in the range `[start, end)` — i.e. `name.len` is accessed before the slice.
fn lenCheckedBefore(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    if (start >= end) return false;
    var t: Ast.TokenIndex = start;
    // end is exclusive: we scan [start, end-1].
    while (t + 2 < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "len")) continue;
        return true;
    }
    return false;
}

/// Parses the slice offset token slice to a value.  Returns null on anything
/// non-decimal-constant (hex/underscored offsets are rare and conservatively
/// skipped).
fn offsetValue(offset_str: []const u8) ?usize {
    return std.fmt.parseInt(usize, offset_str, 0) catch null;
}

/// If `name` is a local declared in `[first, slice_tok)` as exactly one call
/// expression — `(const|var) name (: T)? = [try] [recv.]CALLEE ( … )` — returns
/// the callee identifier (the name immediately before the call's `(`).  Returns
/// null when the initializer is anything other than a single (possibly dotted /
/// `try`-wrapped) call, so the caller never assumes a postcondition unsoundly.
fn localInitCallee(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    slice_tok: Ast.TokenIndex,
    name: []const u8,
) ?[]const u8 {
    if (first + 2 >= slice_tok) return null;
    var t: Ast.TokenIndex = first;
    while (t + 2 < slice_tok) : (t += 1) {
        if (tags[t] != .keyword_const and tags[t] != .keyword_var) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), name)) continue;

        // Advance to the `=`, allowing an optional `: type` (stop at `;`).
        var j: Ast.TokenIndex = t + 2;
        while (j < slice_tok and tags[j] != .equal and tags[j] != .semicolon) : (j += 1) {}
        if (j >= slice_tok or tags[j] != .equal) return null;
        j += 1;
        if (j < slice_tok and tags[j] == .keyword_try) j += 1;

        // Expect a (possibly dotted) name followed by `(`.
        if (j >= slice_tok or tags[j] != .identifier) return null;
        var callee = tree.tokenSlice(j);
        var k: Ast.TokenIndex = j + 1;
        while (k + 1 < slice_tok and tags[k] == .period and tags[k + 1] == .identifier) {
            callee = tree.tokenSlice(k + 1);
            k += 2;
        }
        if (k < slice_tok and tags[k] == .l_paren) return callee;
        return null;
    }
    return null;
}

/// Strongest constant lower bound on `name.len` proven by an access in
/// `[start, end)`, or 0 if none.
///
///   Index access  `name[K]`     → proves `name.len >= K + 1`.
///   Closed slice   `name[A..M]`  → proves `name.len >= M`   (M a literal).
///
/// Open-ended slices `name[K..]` (the very pattern this rule flags) and slices
/// with a non-literal high bound prove nothing and are ignored, so the result
/// is a sound lower bound.  Path-insensitive, like the `.len` heuristic.
fn provenMinLenBefore(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) usize {
    if (start >= end) return 0;
    var best: usize = 0;
    var t: Ast.TokenIndex = start;
    while (t + 1 < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        if (tags[t + 1] != .l_bracket) continue;

        // Find the matching `]` for this subscript, noting an `..` at depth 1.
        var depth: u32 = 0;
        var has_ellipsis = false;
        var k: Ast.TokenIndex = t + 1;
        while (k < end) : (k += 1) {
            if (tags[k] == .l_bracket) {
                depth += 1;
            } else if (tags[k] == .r_bracket) {
                depth -= 1;
                if (depth == 0) break;
            } else if (depth == 1 and tags[k] == .ellipsis2) {
                has_ellipsis = true;
            }
        }
        if (k >= end or tags[k] != .r_bracket or k == 0) continue;

        // The bound comes only from a literal immediately before the `]`.
        if (tags[k - 1] != .number_literal) {
            t = k;
            continue;
        }
        const num = std.fmt.parseInt(usize, tree.tokenSlice(k - 1), 0) catch {
            t = k;
            continue;
        };
        // Closed slice `[A..M]` ⇒ len >= M; index `[K]` ⇒ len >= K + 1.
        const bound: usize = if (has_ellipsis) num else num + 1;
        if (bound > best) best = bound;
        t = k;
    }
    return best;
}

/// Returns true iff a prefix-check call `PREFIXFN(…, name, "literal")` appears
/// in `[start, end)` whose prefix has a byte length >= the slice `offset_str`.
///
/// A prefix check — `mem.startsWith(u8, name, prefix)`, the `bun.strings`
/// `startsWith*` variants, and the `hasPrefix*` family (`hasPrefixComptime`,
/// `hasPrefixCaseInsensitive`) — guarantees `name.len >= prefix.len`.  When
/// `prefix.len >= offset`, the slice `name[offset..]` is in-bounds.  The matched
/// argument shape is `IDENT(name) comma string_literal` at the top level of the
/// call's argument list (so the leading `u8,` of `std.mem.startsWith` is
/// transparently skipped, and nested calls are ignored).  A `char_literal`
/// second argument (`startsWithChar(name, c)`) proves `name.len >= 1` and
/// matches offset 1.
///
/// Path-insensitive, like the `.len` and length lower-bound heuristics: in
/// practice the guard and the slice sit in the same guarded branch.
fn prefixCheckGuardBefore(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
    offset_str: []const u8,
) bool {
    if (start >= end) return false;
    const offset = std.fmt.parseInt(usize, offset_str, 0) catch return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        const fname = tree.tokenSlice(t);
        if (!std.mem.startsWith(u8, fname, "startsWith") and
            !std.mem.startsWith(u8, fname, "hasPrefix")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // Walk the argument list at paren-depth 1, looking for the buffer
        // argument followed by a prefix literal.
        var depth: u32 = 0;
        var k: Ast.TokenIndex = t + 1;
        while (k < end) : (k += 1) {
            if (tags[k] == .l_paren) {
                depth += 1;
            } else if (tags[k] == .r_paren) {
                depth -= 1;
                if (depth == 0) break;
            } else if (depth == 1 and
                k + 2 < end and
                tags[k] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(k), name) and
                tags[k + 1] == .comma)
            {
                if (tags[k + 2] == .string_literal) {
                    if (stringLiteralMinByteLen(tree.tokenSlice(k + 2)) >= offset) return true;
                } else if (tags[k + 2] == .char_literal and offset == 1) {
                    return true;
                }
            }
        }
    }
    return false;
}

/// Returns true iff `name` is declared in `[start, end)` as a local fixed-size
/// array — i.e. its element count is a compile-time constant.  Two forms:
///
///   Array type:    `(const|var) name : [ NUMBER ] …`     (e.g. `[48]u8`)
///   Array literal: `(const|var) name … = [ (_ | NUMBER) ] …`  (e.g. `[_]u8{…}`)
///
/// Slice types (`: []T`), many-item pointers (`: [*]T`), and sentinel slices
/// (`: [:0]T`) are NOT arrays — they have no `number_literal` immediately after
/// `[`, so they are correctly excluded.  Slicing a fixed-size array is
/// compile-time bounds checked, so any `name[N..]` that compiles has N <= K.
fn isLocalFixedArray(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    if (start >= end) return false;
    var k: Ast.TokenIndex = start;
    while (k + 1 < end) : (k += 1) {
        if (tags[k] != .keyword_const and tags[k] != .keyword_var) continue;
        if (tags[k + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k + 1), name)) continue;

        // Form A — array type annotation: `name : [ NUMBER ]`.
        if (k + 4 < end and
            tags[k + 2] == .colon and
            tags[k + 3] == .l_bracket and
            tags[k + 4] == .number_literal) return true;

        // Form B — array literal initializer: `name (: type)? = [ (_ | NUMBER) ]`.
        // Scan forward to the `=` (stopping at the statement's `;`).
        var j: Ast.TokenIndex = k + 2;
        while (j + 3 < end and tags[j] != .semicolon) : (j += 1) {
            if (tags[j] != .equal) continue;
            if (tags[j + 1] != .l_bracket) break; // initializer is not an array literal
            const inner = tags[j + 2];
            const is_inferred = inner == .identifier and std.mem.eql(u8, tree.tokenSlice(j + 2), "_");
            if ((inner == .number_literal or is_inferred) and tags[j + 3] == .r_bracket) return true;
            break;
        }
    }
    return false;
}

/// Returns true iff `name` is declared as a `comptime` parameter in `proto`.
/// A comptime parameter has `p.comptime_noalias` set to a `.keyword_comptime`
/// token.  Slicing a comptime slice is compile-time bounds checked per
/// instantiation — a caller passing a too-short literal would be a compile
/// error, not a runtime OOB.
fn isComptimeParam(
    proto: Ast.full.FnProto,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    name: []const u8,
) bool {
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        const nt = p.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), name)) continue;
        if (p.comptime_noalias) |tok| {
            return tags[tok] == .keyword_comptime;
        }
    }
    return false;
}

/// Lower bound on the decoded byte length of a Zig string-literal token slice
/// (quotes included).  Each escape sequence counts as >= 1 byte; `\u{…}` may
/// decode to more, so the result is a sound lower bound for a `>= offset` test.
fn stringLiteralMinByteLen(slice: []const u8) usize {
    if (slice.len < 2) return 0;
    const content = slice[1 .. slice.len - 1];
    var i: usize = 0;
    var count: usize = 0;
    while (i < content.len) {
        if (content[i] == '\\') {
            i += 1;
            if (i >= content.len) break;
            switch (content[i]) {
                'x' => i += 3, // \xNN
                'u' => { // \u{...}
                    i += 1;
                    while (i < content.len and content[i] != '}') i += 1;
                    i += 1;
                },
                else => i += 1, // \n \t \\ \" \' \r etc.
            }
            count += 1;
        } else {
            i += 1;
            count += 1;
        }
    }
    return count;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    lb_tok: Ast.TokenIndex,
    buf_name: []const u8,
    offset: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}[{s}..]` slices from a fixed offset without a prior `{s}.len >= {s}` check — crashes (Debug/Safe) or UB (ReleaseFast) when the slice is shorter than {s} bytes; add `if ({s}.len < {s}) return error.TruncatedInput;` before this slice",
        .{ buf_name, offset, buf_name, offset, offset, buf_name, offset },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, lb_tok),
        .end = try Pos.fromTokenEnd(tree, lb_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "slice-from-fixed-offset-without-len-check: basic pattern fires" {
    try testing.expectFires(check, R,
        \\fn parse(line: []const u8) []const u8 {
        \\    return line[6..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: larger offset fires" {
    try testing.expectFires(check, R,
        \\fn parse(header: []const u8) []const u8 {
        \\    return header[10..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: zero offset does not fire" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8) []const u8 {
        \\    return buf[0..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: len check before slice suppresses" {
    try testing.expectNoFire(check,
        \\fn parse(line: []const u8) ![]const u8 {
        \\    if (line.len < 6) return error.TruncatedInput;
        \\    return line[6..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: chained field access does not fire" {
    try testing.expectNoFire(check,
        \\const S = struct {
        \\    buf: []const u8,
        \\    pub fn tail(self: S) []const u8 {
        \\        return self.buf[4..];
        \\    }
        \\};
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: len consulted anywhere before suppresses" {
    try testing.expectNoFire(check,
        \\fn f(data: []const u8) []const u8 {
        \\    const n = data.len;
        \\    _ = n;
        \\    return data[4..];
        \\}
        \\
    );
}

// ── Self-advance / consume idiom suppression ────────────────

test "slice-from-fixed-offset-without-len-check: self-advance buf = buf[1..] does not fire" {
    try testing.expectNoFire(check,
        \\fn consume(items: []u32) void {
        \\    var remain = items;
        \\    for (items) |it| {
        \\        remain[0] = it;
        \\        remain = remain[1..];
        \\    }
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: self-advance with larger offset does not fire" {
    try testing.expectNoFire(check,
        \\fn skip(input: []const u8) []const u8 {
        \\    var name = input;
        \\    name = name[4..];
        \\    return name;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: assignment to a different var still fires" {
    try testing.expectFires(check, R,
        \\fn f(key: []const u8) []const u8 {
        \\    var out = key[1..];
        \\    return out;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: field assign sharing local name still fires" {
    try testing.expectFires(check, R,
        \\const S = struct { buf: []const u8 };
        \\fn f(s: *S, buf: []const u8) void {
        \\    s.buf = buf[2..];
        \\}
        \\
    );
}

// ── length lower-bound from index / closed-end-slice accesses ──

test "slice-from-fixed-offset-without-len-check: buf[0] access before offset-1 slice suppresses" {
    try testing.expectNoFire(check,
        \\fn f(name: []const u8) []const u8 {
        \\    if (name[0] == '@') {
        \\        return name[1..];
        \\    }
        \\    return name;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: buf[0] access does NOT suppress offset-2 slice" {
    try testing.expectFires(check, R,
        \\fn f(name: []const u8) []const u8 {
        \\    _ = name[0];
        \\    return name[2..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: buf[0..] slice does not count as a [0] proof" {
    try testing.expectFires(check, R,
        \\fn f(name: []const u8) []const u8 {
        \\    const head = name[0..];
        \\    _ = head;
        \\    return name[1..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: closed-end slice buf[0..4] suppresses buf[4..]" {
    try testing.expectNoFire(check,
        \\fn f(buf: []u8) []u8 {
        \\    buf[0..4].* = .{ 0, 0, 0, 0 };
        \\    return buf[4..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: index buf[2] proves len>=3, suppresses buf[2..]" {
    try testing.expectNoFire(check,
        \\fn f(arguments: []const Value) void {
        \\    if (arguments[2].isObject()) {
        \\        use(arguments[2..]);
        \\    }
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: bound below offset still fires" {
    try testing.expectFires(check, R,
        \\fn f(buf: []u8) []u8 {
        \\    buf[0..3].* = .{ 0, 0, 0 };
        \\    return buf[4..];
        \\}
        \\
    );
}

// ── startsWith-guard length guarantee ───────────────────────

test "slice-from-fixed-offset-without-len-check: startsWith(u8, x, \"--\") suppresses x[2..]" {
    try testing.expectNoFire(check,
        \\fn parse(arg: []const u8) []const u8 {
        \\    if (std.mem.startsWith(u8, arg, "--")) return arg[2..];
        \\    return arg;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: namespaced startsWith with long prefix suppresses x[8..]" {
    try testing.expectNoFire(check,
        \\fn trim(name_ref: []const u8) []const u8 {
        \\    if (bun.strings.startsWithCaseInsensitiveAscii(name_ref, "-webkit-")) {
        \\        return name_ref[8..];
        \\    }
        \\    return name_ref;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: startsWith prefix shorter than offset still fires" {
    try testing.expectFires(check, R,
        \\fn parse(arg: []const u8) []const u8 {
        \\    if (std.mem.startsWith(u8, arg, "-")) return arg[4..];
        \\    return arg;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: startsWith on a different buffer still fires" {
    try testing.expectFires(check, R,
        \\fn parse(arg: []const u8, other: []const u8) []const u8 {
        \\    if (std.mem.startsWith(u8, other, "--")) return arg[2..];
        \\    return arg;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: hasPrefixComptime guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(utf8: []const u8) []const u8 {
        \\    if (strings.hasPrefixComptime(utf8, "\\\\")) {
        \\        return utf8[2..];
        \\    }
        \\    return utf8;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: hasPrefixComptime with hex-escape BOM suppresses offset 3" {
    try testing.expectNoFire(check,
        \\fn f(buffer_slice: []const u8) []const u8 {
        \\    if (strings.hasPrefixComptime(buffer_slice, "\xef\xbb\xbf")) {
        \\        return buffer_slice[3..];
        \\    }
        \\    return buffer_slice;
        \\}
        \\
    );
}

// ── Local fixed-size array (Tier 3 declaration tracking) ────

test "slice-from-fixed-offset-without-len-check: sized-array local does not fire" {
    try testing.expectNoFire(check,
        \\fn f() void {
        \\    var buf: [48]u8 = undefined;
        \\    const tail = buf[7..];
        \\    _ = tail;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: inferred-length array literal local does not fire" {
    try testing.expectNoFire(check,
        \\fn f() void {
        \\    var decimal_buf = [_]u8{ '.', 0 };
        \\    const rest = decimal_buf[1..];
        \\    _ = rest;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: slice-typed local still fires" {
    try testing.expectFires(check, R,
        \\fn f(input: []const u8) void {
        \\    const buf: []const u8 = input;
        \\    const tail = buf[7..];
        \\    _ = tail;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: slice derived from a fixed array has known extent" {
    try testing.expectNoFireTyped(check,
        \\fn f() void {
        \\    var arr: [48]u8 = undefined;
        \\    const sub = arr[0..];
        \\    const tail = sub[7..];
        \\    _ = tail;
        \\}
        \\
    );
}

// ── Cross-fn 1-hop return-length postcondition ──────────────

test "slice-from-fixed-offset-without-len-check: 1-hop callee returning literals suppresses" {
    try testing.expectNoFire(check,
        \\fn tag() []const u8 {
        \\    return "</script";
        \\}
        \\fn f() []const u8 {
        \\    const t = tag();
        \\    return t[2..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 1-hop return-switch literals suppresses" {
    try testing.expectNoFire(check,
        \\fn tag(kind: u8) []const u8 {
        \\    return switch (kind) {
        \\        0 => "</script",
        \\        1 => "</style",
        \\        else => unreachable,
        \\    };
        \\}
        \\fn f(kind: u8) []const u8 {
        \\    const t = tag(kind);
        \\    return t[2..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 1-hop offset beyond postcondition still fires" {
    try testing.expectFires(check, R,
        \\fn tag() []const u8 {
        \\    return "ab";
        \\}
        \\fn f() []const u8 {
        \\    const t = tag();
        \\    return t[4..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 1-hop callee with unbounded return still fires" {
    try testing.expectFires(check, R,
        \\fn passthrough(x: []const u8) []const u8 {
        \\    return x;
        \\}
        \\fn f(input: []const u8) []const u8 {
        \\    const t = passthrough(input);
        \\    return t[2..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 1-hop name collision with unbounded def stays firing" {
    try testing.expectFires(check, R,
        \\const A = struct {
        \\    fn tag(self: A) []const u8 {
        \\        _ = self;
        \\        return "</script";
        \\    }
        \\};
        \\const B = struct {
        \\    payload: []const u8,
        \\    fn tag(self: B) []const u8 {
        \\        return self.payload;
        \\    }
        \\};
        \\fn f(b: B) []const u8 {
        \\    const t = b.tag();
        \\    return t[2..];
        \\}
        \\
    );
}

// ── Cross-fn 2-hop param-from-caller propagation ────────────

test "slice-from-fixed-offset-without-len-check: 2-hop param fed only literal-returning calls suppresses" {
    try testing.expectNoFire(check,
        \\fn closingTag(kind: u8) []const u8 {
        \\    return switch (kind) {
        \\        0 => "</script",
        \\        else => "</style",
        \\    };
        \\}
        \\fn countTags(content: []const u8, close_tag: []const u8) usize {
        \\    const suffix = close_tag[2..];
        \\    _ = content;
        \\    return suffix.len;
        \\}
        \\fn caller(content: []const u8, kind: u8) usize {
        \\    return countTags(content, closingTag(kind));
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 2-hop fires when a caller passes an unbounded arg" {
    try testing.expectFires(check, R,
        \\fn closingTag() []const u8 {
        \\    return "</script";
        \\}
        \\fn countTags(close_tag: []const u8) usize {
        \\    return close_tag[2..].len;
        \\}
        \\fn callerA() usize {
        \\    return countTags(closingTag());
        \\}
        \\fn callerB(runtime: []const u8) usize {
        \\    return countTags(runtime);
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 2-hop string-literal callers suppress" {
    try testing.expectNoFire(check,
        \\fn skipDashes(arg: []const u8) []const u8 {
        \\    return arg[2..];
        \\}
        \\fn a() []const u8 {
        \\    return skipDashes("--foo");
        \\}
        \\fn b() []const u8 {
        \\    return skipDashes("--barbaz");
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: 2-hop does not suppress pub fn (external callers unseen)" {
    try testing.expectFires(check, R,
        \\pub fn skipDashes(arg: []const u8) []const u8 {
        \\    return arg[2..];
        \\}
        \\fn a() []const u8 {
        \\    return skipDashes("--foo");
        \\}
        \\
    );
}

// ── comptime parameter suppression ────────────────────────────────────────

test "slice-from-fixed-offset-without-len-check: comptime slice param does not fire" {
    try testing.expectNoFire(check,
        \\fn eatLiteral(s: []const u8, comptime literal: []const u8) []const u8 {
        \\    const rest = literal[1..];
        \\    _ = s;
        \\    return rest;
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: comptime type param does not fire" {
    try testing.expectNoFire(check,
        \\fn eat(comptime fmt: []const u8) void {
        \\    _ = fmt[2..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: non-comptime param with same name still fires" {
    try testing.expectFires(check, R,
        \\fn parse(literal: []const u8) []const u8 {
        \\    return literal[1..];
        \\}
        \\
    );
}

test "slice-from-fixed-offset-without-len-check: checked ELF header return lengths" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn objectSlice(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8) !void {
        \\    if (bytes.len < 64) return error.Invalid;
        \\    if (!std.mem.eql(u8, bytes[0..4], "\x7fELF")) return error.Invalid;
        \\    const is_64: bool = switch (bytes[4]) {
        \\        1 => false,
        \\        2 => true,
        \\        else => return error.Invalid,
        \\    };
        \\    if (bytes[5] != 1) return error.Invalid;
        \\    const header = try objectSlice(bytes, 0, if (is_64) @as(usize, 64) else @as(usize, 52));
        \\    const shoff: usize = if (is_64)
        \\        @intCast(std.mem.readInt(u64, header[40..][0..8], .little))
        \\    else
        \\        std.mem.readInt(u32, header[32..][0..4], .little);
        \\    const shentsize: usize = if (is_64)
        \\        std.mem.readInt(u16, header[58..][0..2], .little)
        \\    else
        \\        std.mem.readInt(u16, header[46..][0..2], .little);
        \\    const shnum: usize = if (is_64)
        \\        std.mem.readInt(u16, header[60..][0..2], .little)
        \\    else
        \\        std.mem.readInt(u16, header[48..][0..2], .little);
        \\    const shstrndx: usize = if (is_64)
        \\        std.mem.readInt(u16, header[62..][0..2], .little)
        \\    else
        \\        std.mem.readInt(u16, header[50..][0..2], .little);
        \\    _ = .{ shoff, shentsize, shnum, shstrndx };
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: checked ELF table entry extents" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn objectSlice(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8, shoff: usize, shentsize: usize, shnum: usize, shstrndx: usize, is_64: bool) !u64 {
        \\    const entry_size: usize = if (is_64) 64 else 40;
        \\    if (shentsize != entry_size) return error.Invalid;
        \\    if (shnum == 0 or shnum > 4096) return error.Invalid;
        \\    if (shstrndx >= shnum) return error.Invalid;
        \\    const table = try objectSlice(bytes, shoff, shnum * entry_size);
        \\    const strings_entry = table[shstrndx * entry_size ..][0..entry_size];
        \\    const strings_offset: usize = if (is_64)
        \\        @intCast(std.mem.readInt(u64, strings_entry[24..][0..8], .little))
        \\    else
        \\        std.mem.readInt(u32, strings_entry[16..][0..4], .little);
        \\    const strings_size: usize = if (is_64)
        \\        @intCast(std.mem.readInt(u64, strings_entry[32..][0..8], .little))
        \\    else
        \\        std.mem.readInt(u32, strings_entry[20..][0..4], .little);
        \\    _ = .{ strings_offset, strings_size };
        \\    var section_index: usize = 0;
        \\    while (section_index < shnum) : (section_index += 1) {
        \\        const entry = table[section_index * entry_size ..][0..entry_size];
        \\        const name_offset = std.mem.readInt(u32, entry[0..][0..4], .little);
        \\        if (name_offset != 1) continue;
        \\        if (is_64) {
        \\            return std.mem.readInt(u64, entry[32..][0..8], .little);
        \\        }
        \\        return std.mem.readInt(u32, entry[20..][0..4], .little);
        \\    }
        \\    return error.Invalid;
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: dynamic table repro" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn read(table: []const u8, count: u16, index: u16, is_64: bool) !u64 {
        \\    const entry_size: usize = if (is_64) 64 else 40;
        \\    if (count == 0 or index >= count) return error.Invalid;
        \\    if (table.len != @as(usize, count) * entry_size) return error.Invalid;
        \\    const entry = table[@as(usize, index) * entry_size ..][0..entry_size];
        \\    return if (is_64) std.mem.readInt(u64, entry[32..][0..8], .little)
        \\        else std.mem.readInt(u32, entry[20..][0..4], .little);
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: checked return bound is insufficient" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8) ![]const u8 {
        \\    const header = try bounded(bytes, 0, 51);
        \\    return header[62..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: conditional return length needs matching branch" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8, is_64: bool) ![]const u8 {
        \\    const header = try bounded(bytes, 0, if (is_64) @as(usize, 64) else @as(usize, 52));
        \\    return header[62..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: opposite return length branch remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8, is_64: bool) ![]const u8 {
        \\    const header = try bounded(bytes, 0, if (is_64) @as(usize, 52) else @as(usize, 64));
        \\    if (is_64) return header[62..];
        \\    return header;
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: rebound checked slice loses extent" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8, shorter: []const u8) ![]const u8 {
        \\    var header = try bounded(bytes, 0, 64);
        \\    header = shorter;
        \\    return header[62..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: mutated selector cannot correlate old extent" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8, selector: bool) ![]const u8 {
        \\    var is_64 = selector;
        \\    const header = try bounded(bytes, 0, if (is_64) @as(usize, 64) else @as(usize, 52));
        \\    is_64 = true;
        \\    if (is_64) return header[62..];
        \\    return header;
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: unknown helper return is not requested length" {
    try testing.expectFiresTyped(check, R,
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    _ = .{ offset, len };
        \\    return bytes;
        \\}
        \\pub fn read(bytes: []const u8) ![]const u8 {
        \\    const header = try bounded(bytes, 0, 64);
        \\    return header[62..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: helper short success return poisons extent" {
    try testing.expectFiresTyped(check, R,
        \\fn bounded(bytes: []const u8, len: usize, short: bool) ![]const u8 {
        \\    if (short) return "";
        \\    return bytes[0..len];
        \\}
        \\pub fn read(bytes: []const u8, short: bool) ![]const u8 {
        \\    const header = try bounded(bytes, 64, short);
        \\    return header[62..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: dynamic entry insufficient extent" {
    try testing.expectFiresTyped(check, R,
        \\pub fn read(table: []const u8, is_64: bool) []const u8 {
        \\    const entry_size: usize = if (is_64) 24 else 16;
        \\    const entry = table[0..entry_size];
        \\    return entry[32..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: dynamic entry wrong branch" {
    try testing.expectFiresTyped(check, R,
        \\pub fn read(table: []const u8, is_64: bool) []const u8 {
        \\    const entry_size: usize = if (is_64) 16 else 64;
        \\    const entry = table[0..entry_size];
        \\    if (is_64) return entry[32..];
        \\    return entry;
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: dynamic entry rebind invalidates extent" {
    try testing.expectFiresTyped(check, R,
        \\pub fn read(table: []const u8, shorter: []const u8, is_64: bool) []const u8 {
        \\    const entry_size: usize = if (is_64) 64 else 40;
        \\    var entry = table[0..entry_size];
        \\    entry = shorter;
        \\    return entry[32..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: checked header repro" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn objectSlice(bytes: []const u8, offset: usize, len: usize) ![]const u8 {
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\pub fn read(bytes: []const u8, is_64: bool) !u16 {
        \\    if (bytes.len < 64) return error.Invalid;
        \\    const header = try objectSlice(bytes, 0, if (is_64) @as(usize, 64) else @as(usize, 52));
        \\    return if (is_64) std.mem.readInt(u16, header[62..][0..2], .little)
        \\        else std.mem.readInt(u16, header[50..][0..2], .little);
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: endpoint growth does not resize old entry" {
    try testing.expectFiresTyped(check, R,
        \\pub fn read(table: []const u8) []const u8 {
        \\    var entry_size: usize = 16;
        \\    const entry = table[0..entry_size];
        \\    entry_size = 64;
        \\    return entry[32..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: endpoint mutation preserves existing extent" {
    try testing.expectNoFireTyped(check,
        \\pub fn read(table: []const u8) []const u8 {
        \\    var entry_size: usize = 64;
        \\    const entry = table[0..entry_size];
        \\    entry_size = 0;
        \\    return entry[32..];
        \\}
    );
}

test "slice-from-fixed-offset-without-len-check: addressed entry header mutation loses extent" {
    try testing.expectFiresTyped(check, R,
        \\fn shrink(entry: *[]const u8) void {
        \\    entry.* = "";
        \\}
        \\pub fn read(table: []const u8, is_64: bool) []const u8 {
        \\    const entry_size: usize = if (is_64) 64 else 40;
        \\    var entry = table[0..entry_size];
        \\    shrink(&entry);
        \\    return entry[32..];
        \\}
    );
}
