//! Bounded numeric expression evaluation over resolved types and path facts.
const std = @import("std");
const Ast = std.zig.Ast;
const numbers = @import("numeric_range.zig");
const FileCache = @import("../cache/file_cache.zig").FileCache;
const Range = numbers.Range;
const budget_mod = @import("../budget.zig");
const local_bindings = @import("../model/local_bindings.zig");
const tokens = @import("../ast/tokens.zig");

/// A named value together with the range it was proved to hold: the shape
/// every range fact in this module takes.  It carries no claim of its own
/// about WHAT the range describes — `facts` reads it as the value of the
/// path, `len_bounds` reads it as the length of the binding — so the two
/// tables stay separate and a length is never mistaken for the slice.
pub const Fact = struct { name: []const u8, value: Range };

/// The root-scope `const` declarations a use may name, and what each is
/// initialised to.
///
/// A compile-time integer is routinely written as a name the file defines —
/// `const max_u32 = std.math.maxInt(u32);`, `const VLEN: usize = 64;` — and
/// the type engine resolves the expression inside such a binding but not the
/// name around it.  The declarations are BORROWED from the file cache's one
/// per-file index (`FileCache.fileConstInitializer`), which is built once per
/// file and answers a name directly; nothing here is allocated, and no
/// consumer builds a second table.
///
/// Two answers are deliberately withheld, and both are about a NAME rather
/// than about a value:
///
///   - A name the asking walk binds itself is asked of the walk, not of the
///     file.  A local of the same name is a different value whose facts the
///     walk already holds, so the file-level declaration must not answer for
///     it.  The root tier alone cannot decide that, which is why the walk's
///     own bindings travel with the cache handle.
///   - A name the file declares twice answers nothing.  That rule belongs to
///     the table itself, which drops such a name (and stays dropped, so a
///     third declaration cannot revive it) rather than resolving to whichever
///     declaration happened to come last.  A `const X: T;` with no
///     initializer is recorded the same way: it binds a name without
///     declaring a value this file can read.
pub const ContainerConsts = struct {
    tree: *const Ast,
    /// The cache holding the per-file constant index.  Borrowed, not owned:
    /// the table lives as long as the analysis of this file does.
    cache: *FileCache,
    /// The names this walk binds, borrowed from the walk's own bindings.
    walk_binds: []const local_bindings.Binding,

    pub fn lookup(self: ContainerConsts, name: []const u8) ?Ast.Node.Index {
        for (self.walk_binds) |binding| {
            if (std.mem.eql(u8, binding.name, name)) return null;
        }
        // A table that could not be allocated is not a file with no constants
        // in it: it is a file whose constants cannot be proven.  The name
        // answers nothing, which leaves it to its declared type — the weaker
        // reading, and never a claim the failed allocation invented.
        return (self.cache.fileConstInitializer(name) catch null) orelse null;
    }
};

pub const Evaluator = struct {
    /// The frame cap every descent in the numeric analysis shares: the
    /// evaluator's own recursion, and the statement walk's.
    pub const frame_cap: u8 = 64;

    pub const FloatFormats = struct { minimum: u16, maximum: u16 };

    tree: *const Ast,
    cache: ?*FileCache,
    /// The actual callee frame of a contextual return walk. Root walks use
    /// the cache's resolver; contextual types must not reuse its root answers.
    resolution_frame: ?@import("../type_resolver.zig").TypeResolver.ResolutionFrame = null,
    facts: []const Fact,
    budget: *u32,
    std_valid: bool,
    depth: u8 = 0,
    /// Closed generic instantiations may prove a format span without proving
    /// one format. Null keeps unresolved conversions unbounded.
    float_formats: ?struct {
        context: *anyopaque,
        bounds: *const fn (*anyopaque, Ast.Node.Index) ?FloatFormats,
    } = null,
    /// File-scope `const` bindings, when the caller could resolve which of
    /// them this walk may name.  Null leaves an identifier to its declared
    /// type, which is the weaker but never wrong reading.
    container_consts: ?ContainerConsts = null,
    /// Range snapshots of a local's LENGTH, keyed by the local's own name.
    ///
    /// A standard allocator's `alloc(T, n)` returns exactly `n` elements, so
    /// the length of the binding it produced IS the count — and the count is
    /// a RANGE, not a constant: `@as(usize, v)` over a `u32` capture is
    /// every value up to 2^32-1, which is a narrower answer than the slice's
    /// own `usize` and a wider one than the allocator was ever asked about.
    ///
    /// The snapshot is taken where the binding was established and is owned
    /// by the walk's state, not re-read from the count's name: a write to
    /// the binding, or to the count it was given, drops the entry rather than
    /// leaving a length behind that describes a value no longer there.  It
    /// is deliberately NOT part of `facts`: a fact there is the value of the
    /// path itself, and the length of a slice is not the slice.
    len_bounds: []const Fact = &.{},
    /// State-dependent header bounds, including extents selected by a retained
    /// success fact. The callback borrows the state; no copied fact table is
    /// needed to activate a conditional extent.
    length_bounds: ?struct {
        context: *const anyopaque,
        bound: *const fn (context: *const anyopaque, name: []const u8) ?Range,
    } = null,

    /// Frames a recursive descent may take before it declines to go deeper.
    /// The owning walk spends the same bound on its own descents, so the two
    /// stop at the same depth and the diagnostic names one number.
    depth_limit: u8 = frame_cap,
    /// The step budget the owning query started with, reported when this
    /// evaluator runs the counter to zero.  The remaining count alone cannot
    /// say what the bound in force was.
    budget_cap: u32 = 0,
    /// Where the owning walk records the bound that stopped it.  Depth and
    /// steps are different bounds and the record has to say which one ran
    /// out: writing the step counter on the depth path would report a cost
    /// limit for a walk that spent a few dozen steps and stopped on nesting.
    stopped: ?*?budget_mod.Stop = null,
    /// Metadata/source failures are not missing numeric proofs. The owning
    /// throwing query returns the first error before publishing its answer.
    query_error: ?*?@import("../cache/file_cache.zig").SummaryError = null,

    /// Record the bound that stopped this evaluator.  First stop wins: a walk
    /// that gives up keeps unwinding and may trip a second bound, but the
    /// first one is the one that explains the rest.  The step counter is
    /// emptied as well, because a bound that stopped this expression has
    /// stopped everything computed from it.
    fn noteStop(self: *Evaluator, limit: budget_mod.Limit, cap: u32) void {
        self.budget.* = 0;
        if (self.stopped) |record| {
            if (record.* == null) record.* = .{ .limit = limit, .cap = cap };
        }
    }

    pub fn evaluate(self: *Evaluator, original: Ast.Node.Index) Range {
        if (self.depth >= self.depth_limit) {
            self.noteStop(.numeric_oracle_depth, self.depth_limit);
            return .unknown;
        }
        if (self.budget.* == 0) {
            self.noteStop(.numeric_oracle_steps, self.budget_cap);
            return .unknown;
        }
        self.budget.* -= 1;
        self.depth += 1;
        defer self.depth -= 1;
        const node = ungroup(self.tree, original);
        if (path(self.tree, node)) |name| {
            for (self.facts) |fact| {
                if (!std.mem.eql(u8, fact.name, name)) continue;
                // An assignment the walk could not evaluate records "this name
                // says nothing here", which is not the same claim as "this
                // name's type says nothing".  Falling through lets the
                // declared type bound it again, so `x = <unresolved call>`
                // keeps the parameter's or field's own range instead of
                // losing it to the absence of knowledge.
                if (fact.value == .unknown) continue;
                return self.narrow(fact.value, node);
            }
        }
        return switch (self.tree.nodeTag(node)) {
            .number_literal => self.literal(node),
            .negation => self.evaluate(self.tree.nodeData(node).node).negate(),
            .identifier, .field_access, .deref => self.declaredRange(node),
            .@"try" => self.evaluate(self.tree.nodeData(node).node),
            .add, .sub, .mul, .div => self.arithmetic(node),
            .mod => self.modulo(node),
            .bit_and, .bit_or, .bit_xor => self.bitwise(node),
            .shl, .shr => self.shift(node),
            .@"switch", .switch_comma => self.switchExpression(node),
            .@"if", .if_simple => self.conditionalExpression(node),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => self.builtinCall(node),
            .call, .call_comma, .call_one, .call_one_comma => self.standardCall(node),
            else => self.typeRange(node),
        };
    }

    /// The extent of a container expression, not the numeric value of its header.
    /// Local slices use snapshots from the current walk; only fixed types and
    /// immutable file constants can supply extents without that state.
    pub fn containerLength(self: *Evaluator, original: Ast.Node.Index) Range {
        if (self.depth >= self.depth_limit) {
            self.noteStop(.numeric_oracle_depth, self.depth_limit);
            return .unknown;
        }
        if (self.budget.* == 0) {
            self.noteStop(.numeric_oracle_steps, self.budget_cap);
            return .unknown;
        }
        self.budget.* -= 1;
        self.depth += 1;
        defer self.depth -= 1;
        const node = ungroup(self.tree, original);
        if (self.cache) |cache| {
            if (cache.zls) |resolver| {
                const length = resolver.fixedArrayLen(node) catch |err| {
                    _ = self.failedQuery(err);
                    return .unknown;
                };
                if (length) |known| return Range.constant(known);
            }
        }
        var projected: Range = self.allocatedLengthBound(node) orelse .unknown;
        if (path(self.tree, node)) |name| {
            for (self.facts) |fact| {
                if (fact.name.len != name.len + ".len".len or
                    !std.mem.startsWith(u8, fact.name, name) or
                    !std.mem.endsWith(u8, fact.name, ".len")) continue;
                projected = projected.intersect(fact.value);
            }
        }
        if (projected == .integer) return projected;
        if (self.tree.nodeTag(node) == .identifier) {
            const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
            if (self.fileConstantInitializer(name)) |initializer| return self.containerLength(initializer);
        }
        if (self.tree.nodeTag(node) == .field_access) {
            const length = self.constantMemberLength(node);
            if (length != .unknown) return length;
        }
        var array_buffer: [2]Ast.Node.Index = undefined;
        if (self.tree.fullArrayInit(&array_buffer, node)) |array|
            return Range.constant(@intCast(array.ast.elements.len));
        if (self.tree.nodeTag(node) == .address_of) {
            const child = ungroup(self.tree, self.tree.nodeData(node).node);
            if (self.tree.fullArrayInit(&array_buffer, child)) |array|
                return Range.constant(@intCast(array.ast.elements.len));
        }
        if (self.tree.nodeTag(node) == .string_literal) {
            var writer: std.Io.Writer.Discarding = .init(&.{});
            const result = std.zig.string_literal.parseWrite(
                &writer.writer,
                self.tree.tokenSlice(self.tree.nodeMainToken(node)),
            ) catch return .unknown;
            return switch (result) {
                .success => Range.constant(writer.count),
                .failure => .unknown,
            };
        }
        if (self.tree.nodeTag(node) == .multiline_string_literal) {
            const start, const end = self.tree.nodeData(node).token_and_token;
            var length: u64 = 0;
            for (start..end + 1, 0..) |token, index| {
                length += self.tree.tokenSlice(@intCast(token)).len - 2 + @intFromBool(index != 0);
            }
            return Range.constant(length);
        }
        var builtin_buffer: [2]Ast.Node.Index = undefined;
        if (self.tree.builtinCallParams(&builtin_buffer, node)) |args| {
            if (args.len == 2 and std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(node)), "@as"))
                return self.containerLength(args[1]);
            if (args.len == 1 and std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(node)), "@embedFile")) {
                const cache = self.cache orelse return .unknown;
                const length = cache.embeddedFileLength(node) catch |err| {
                    if (self.query_error) |record| record.* = record.* orelse err;
                    return .unknown;
                };
                return if (length) |known| Range.constant(known) else .unknown;
            }
        }
        if (self.sliceSourceBound(node)) |bound| return bound;
        return .unknown;
    }

    fn fileConstantInitializer(self: *Evaluator, name: []const u8) ?Ast.Node.Index {
        const consts = self.container_consts orelse return null;
        for (consts.walk_binds) |binding| {
            if (std.mem.eql(u8, binding.name, name)) return null;
        }
        return consts.cache.fileConstInitializer(name) catch |err| {
            _ = self.failedQuery(err);
            return null;
        };
    }

    /// A member name alone says nothing about an extent. Resolve its type
    /// owner in the lexical frame, then read only that owner's immutable
    /// literal declaration, including a module's root declarations.
    fn constantMemberLength(self: *Evaluator, node: Ast.Node.Index) Range {
        const resolver = (self.cache orelse return .unknown).zls orelse return .unknown;
        const parts = self.tree.nodeData(node).node_and_token;
        const frame = self.resolution_frame orelse resolver.resolutionFrame();
        const owner = (frame.resolveValueOfNode(parts[0]) catch |err| {
            _ = self.failedQuery(err);
            return .unknown;
        }) orelse return .unknown;
        if (!owner.is_type_val or owner.data != .container) return .unknown;
        const container = owner.data.container;
        const tree = &container.scope_handle.handle.document.tree;
        if (tree.errors.len != 0) {
            _ = self.failedQuery(error.InvalidSyntax);
            return .unknown;
        }
        var container_buffer: [2]Ast.Node.Index = undefined;
        const members = if (container.scope_handle.scope == .root)
            tree.rootDecls()
        else
            (tree.fullContainerDecl(&container_buffer, container.scope_handle.toNode()) orelse return .unknown).ast.members;
        const name = self.tree.tokenSlice(parts[1]);
        var initializer: ?Ast.Node.Index = null;
        for (members) |member| {
            if (self.budget.* == 0) {
                self.noteStop(.numeric_oracle_steps, self.budget_cap);
                return .unknown;
            }
            self.budget.* -= 1;
            const declaration = tree.fullVarDecl(member) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(declaration.ast.mut_token + 1), name)) continue;
            if (initializer != null or tree.tokenTag(declaration.ast.mut_token) != .keyword_const)
                return .unknown;
            initializer = declaration.ast.init_node.unwrap() orelse return .unknown;
        }
        var value = ungroup(tree, initializer orelse return .unknown);
        if (tree.nodeTag(value) == .address_of) value = ungroup(tree, tree.nodeData(value).node);
        var array_buffer: [2]Ast.Node.Index = undefined;
        const array = tree.fullArrayInit(&array_buffer, value) orelse return .unknown;
        return Range.constant(array.ast.elements.len);
    }

    pub fn typeRange(self: *Evaluator, node: Ast.Node.Index) Range {
        if (self.resolution_frame) |frame| {
            const info = frame.intInfo(node) catch |err| {
                _ = self.failedQuery(err);
                return .unknown;
            };
            if (info) |integer| return Range.integerType(integer.bits, integer.signed);
            const bits = frame.floatBits(node) catch |err| {
                _ = self.failedQuery(err);
                return .unknown;
            };
            return if (bits != null) .{ .floating = .{} } else .unknown;
        }
        const cache = self.cache orelse return .unknown;
        if (cache.intInfoOf(node)) |info| return Range.integerType(info.bits, info.signed);
        if (cache.isFloatType(node) == true) return .{ .floating = .{} };
        return .unknown;
    }

    pub fn floatBits(self: *Evaluator, node: Ast.Node.Index) ?u16 {
        if (self.resolution_frame) |frame| return frame.floatBits(node) catch |err| {
            _ = self.failedQuery(err);
            return null;
        };
        const cache = self.cache orelse return null;
        const resolver = cache.zls orelse return null;
        return resolver.floatBits(node) catch null;
    }

    /// Canonical parameter identity proves that both values use the same
    /// format at each call, even when the closed calls use different formats.
    pub fn sameTypeParameter(self: *Evaluator, source: Ast.Node.Index, destination: Ast.Node.Index) bool {
        const resolver = (self.cache orelse return false).zls orelse return false;
        const input = (resolver.typeParameterReference(source) catch return false) orelse return false;
        if (source == destination) return true;
        const output = (resolver.typeParameterReference(destination) catch return false) orelse return false;
        return input.tree == output.tree and input.token == output.token;
    }

    fn floatEnvelope(self: *Evaluator, value: Range, node: Ast.Node.Index, operand: ?Ast.Node.Index) Range {
        if (self.floatBits(node)) |bits| return value.asFloat(bits);
        const source = self.float_formats orelse return value.asFloat(0);
        const formats = source.bounds(source.context, node) orelse return value.asFloat(0);
        // Bounds at an unsupported format cannot establish an enclosure.
        switch (formats.minimum) {
            16, 32, 64, 80, 128 => {},
            else => return value.asFloat(0),
        }
        switch (formats.maximum) {
            16, 32, 64, 80, 128 => {},
            else => return value.asFloat(0),
        }
        // Proven widening keeps strict endpoints: rounding them again would
        // turn an excluded integer conversion limit into an included value.
        if (value == .floating) if (operand) |input| {
            if (self.sameTypeParameter(input, node)) return value;
            const input_bits = self.floatBits(input) orelse
                if (source.bounds(source.context, input)) |input_formats| input_formats.maximum else null;
            if (input_bits) |bits| {
                if (bits != 0 and bits <= formats.minimum) return value;
            }
        };
        const supported = [_]u16{ 16, 32, 64, 80, 128 };
        var envelope: ?Range = null;
        for (supported) |bits| {
            if (bits < formats.minimum or bits > formats.maximum) continue;
            const rounded = value.asFloat(bits);
            envelope = if (envelope) |previous| previous.join(rounded) else rounded;
        }
        return envelope orelse value.asFloat(0);
    }

    pub fn coerce(self: *Evaluator, value: Range, source: Ast.Node.Index, destination: Ast.Node.Index) Range {
        if (self.floatBits(destination)) |bits| {
            if (self.floatBits(source)) |source_bits| {
                if (source_bits <= bits and value == .floating) return value;
            }
            return value.asFloat(bits);
        }
        const target = self.typeRange(destination);
        if (target == .integer) return value.intersect(target);
        // A generic destination can narrow a certified finite source to
        // infinity. Round through every proved destination format; missing
        // format evidence must discard the source's finite bounds.
        if (value == .floating or target == .floating)
            return self.floatEnvelope(value, destination, source);
        return value;
    }

    fn literal(self: *Evaluator, node: Ast.Node.Index) Range {
        const text = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        return switch (std.zig.parseNumberLiteral(text)) {
            .int, .big_int => Range.constant(std.fmt.parseInt(i128, text, 0) catch return .unknown),
            .float => Range.floatConstant(std.fmt.parseFloat(f128, text) catch return .unknown)
                .asFloat(self.floatBits(node) orelse 128),
            .failure => .unknown,
        };
    }

    /// What the binding itself says about the node, without consulting any
    /// path fact: a fixed array's own length, a compile-time integer, a
    /// container-level `const` alias, or otherwise the declared type.  This
    /// is the outer bound every fact for the same node is measured against.
    fn declaredRange(self: *Evaluator, node: Ast.Node.Index) Range {
        if (self.tree.nodeTag(node) == .field_access) {
            const parts = self.tree.nodeData(node).node_and_token;
            if (std.mem.eql(u8, self.tree.tokenSlice(parts[1]), "len")) {
                const extent = self.containerLength(parts[0]);
                if (extent != .unknown) {
                    // Read static extents and live header snapshots through
                    // the actual `.len` type when that type can be resolved.
                    const declared = self.typeRange(node);
                    return if (declared == .integer) extent.intersect(declared) else extent;
                }
            }
        }
        if (self.resolution_frame) |frame| {
            const value = frame.resolveValueOfNode(node) catch |err| {
                _ = self.failedQuery(err);
                return .unknown;
            };
            if (value) |actual| if (!actual.is_type_val) {
                if (actual.ipIndex()) |index| {
                    switch (frame.resolver.ctx.ip.indexToKey(index)) {
                        .int_u64_value, .int_i64_value, .int_big_value => {
                            if (frame.resolver.ctx.ip.toInt(index, i128)) |integer|
                                return Range.constant(integer);
                        },
                        else => {},
                    }
                }
            };
        } else if (self.cache) |cache| {
            if (cache.comptimeIntValueOf(node)) |value| return Range.constant(value);
        }
        const declared = self.typeRange(node);
        // A file-scope `const` the file itself defines is the other ordinary
        // spelling of a compile-time integer, and only an identifier can name
        // one.  The table holds no name this walk binds, so what comes back
        // is the value the file gave that name, not a local of the same name.
        if (self.tree.nodeTag(node) == .identifier) {
            const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
            if (self.fileConstantInitializer(name)) |initializer| {
                const value = self.evaluate(initializer);
                if (value == .integer) return value.intersect(declared);
            }
        }
        return declared;
    }

    /// `s[a..b].len` never exceeds `s.len`: a slice's end is checked against
    /// the source's length before the slice exists, and a slice counts
    /// elements from `a` up to at most `b`.  That is the whole of what a
    /// sub-slice says about the source, and it is what lets a bounded input
    /// bound every span cut from it.
    fn sliceSourceBound(self: *Evaluator, node: Ast.Node.Index) ?Range {
        const slice = self.tree.fullSlice(node) orelse return null;
        // A successful ordinary `offset + count` cannot wrap. With the same
        // stable offset on both sides, subtraction cancels it exactly.
        if (path(self.tree, slice.ast.start)) |offset| {
            if (slice.ast.end.unwrap()) |end_node| {
                const end_expr = ungroup(self.tree, end_node);
                if (self.tree.nodeTag(end_expr) == .add) {
                    const left, const right = self.tree.nodeData(end_expr).node_and_node;
                    if (path(self.tree, left)) |left_path| {
                        if (std.mem.eql(u8, offset, left_path) and
                            (path(self.tree, right) != null or self.tree.nodeTag(ungroup(self.tree, right)) == .number_literal))
                        {
                            const count = self.evaluate(right);
                            if (count == .integer and count.integer.min >= 0) return count;
                        }
                    }
                }
            }
        }
        const source = self.containerLength(slice.ast.sliced);
        const start = self.evaluate(slice.ast.start);
        const end = if (slice.ast.end.unwrap()) |end_node| self.evaluate(end_node) else source;
        if (start == .integer and end == .integer and start.integer.min >= 0 and
            end.integer.min >= start.integer.max)
        {
            return .{ .integer = .{
                .min = end.integer.min - start.integer.max,
                .max = end.integer.max - start.integer.min,
            } };
        }
        if (source != .integer) return null;
        return .{ .integer = .{ .min = 0, .max = source.integer.max } };
    }

    /// `local.len` for a local bound to the result of a standard allocator's
    /// `alloc(T, n)`: the range `n` held AT THAT BINDING.
    ///
    /// The allocator's contract is that it returns a slice of exactly `n`
    /// elements, so the count bounds the length from both sides at once —
    /// which is why one snapshot answers what a lower bound alone could not.
    /// The snapshot is a value, not a query: nothing here re-reads the count's
    /// own name, so a count the walk has since learned something new about
    /// cannot widen a length that was proved at the allocation.
    ///
    /// A local the state carries no entry for, or one whose count the walk
    /// could not bound, proves nothing and answers nothing: the length stays
    /// what the declared `usize` says, which is the whole domain and never a
    /// claim that this allocation was small.
    fn allocatedLengthBound(self: *Evaluator, node: Ast.Node.Index) ?Range {
        const name = path(self.tree, node) orelse return null;
        if (self.length_bounds) |bounds| {
            if (bounds.bound(bounds.context, name)) |value|
                if (value != .unknown) return value;
        }
        for (self.len_bounds) |fact| {
            if (!std.mem.eql(u8, fact.name, name)) continue;
            if (fact.value == .unknown) continue;
            return fact.value;
        }
        return null;
    }

    /// A recorded fact narrows the value; the declared type bounds it from
    /// outside.  Intersecting keeps a fact that was established where the
    /// type could not be resolved from widening past the type it was later
    /// resolved to, and keeps a fact from outliving the exact length of the
    /// fixed array it was derived from.  Only two integer ranges are merged:
    /// anything else keeps the fact verbatim rather than losing it to a
    /// variant mismatch.
    fn narrow(self: *Evaluator, fact: Range, node: Ast.Node.Index) Range {
        if (fact != .integer) return fact;
        const declared = self.declaredRange(node);
        if (declared != .integer) return fact;
        return fact.intersect(declared);
    }

    /// A nonnegative integer modulo a positive integer is smaller than the
    /// divisor. Unknown operands and potentially zero divisors prove nothing.
    fn modulo(self: *Evaluator, node: Ast.Node.Index) Range {
        const left_node, const right_node = self.tree.nodeData(node).node_and_node;
        const left = self.evaluate(left_node);
        const right = self.evaluate(right_node);
        if (left != .integer or right != .integer or
            left.integer.min < 0 or right.integer.min <= 0)
        {
            return self.typeRange(node);
        }
        const bound: Range = .{ .integer = .{
            .min = 0,
            .max = @min(left.integer.max, right.integer.max - 1),
        } };
        const declared = self.typeRange(node);
        return if (declared == .integer) bound.intersect(declared) else bound;
    }

    fn arithmetic(self: *Evaluator, node: Ast.Node.Index) Range {
        const parts = self.tree.nodeData(node).node_and_node;
        var left = self.evaluate(parts[0]);
        var right = self.evaluate(parts[1]);
        const precision = self.floatBits(node);
        if (left == .floating or right == .floating) {
            const bits = precision orelse return .{ .floating = .{} };
            left = left.asFloat(bits);
            right = right.asFloat(bits);
        }
        const op: numbers.Operation = switch (self.tree.nodeTag(node)) {
            .add => .add,
            .sub => .sub,
            .mul => .mul,
            .div => .div,
            else => unreachable,
        };
        const value = left.binary(right, op);
        if (value == .floating) return value.asFloat(precision orelse 0);
        // Integer arithmetic does not leave the type it is written in: it
        // traps on overflow in the checked modes and is undefined in the
        // unchecked ones, and there is no value this analysis may name for
        // the result of an operation that can do either.  The mathematical
        // interval is therefore read back through the type only where the
        // operation provably stays inside it; where it may not, the answer is
        // the whole type — never a narrower claim, and never one that reports
        // a value the operation cannot be relied on to produce.  That is what
        // keeps a length bounded by its own guard, `arena.len`, apart from a
        // difference against a snapshot that has no bound of its own.
        const declared = self.typeRange(node);
        if (declared == .integer and value == .integer) {
            return overflowInterval(value.integer, declared.integer);
        }
        return value;
    }

    /// The values `a op b` can be relied on to take, computed inside
    /// `declared`.
    ///
    /// An operation whose mathematical result stays inside the type is
    /// answered exactly.  One that can leave it has no answer narrower than
    /// the type: the overflow traps in the checked modes and is undefined in
    /// the unchecked ones, so no value of it is a fact a reader may use.  The
    /// whole type is the one claim that stays true either way — and it is a
    /// claim about the RESULT's domain, not about wrapping: nothing here says
    /// the operation produces a wrapped value, only that it cannot be shown to
    /// produce anything narrower.  A builtin that wraps by definition
    /// (`+%`, `-%`, `*%`) is the opposite case and is not routed here.
    fn overflowInterval(value: numbers.Integer, declared: numbers.Integer) Range {
        if (value.min >= declared.min and value.max <= declared.max) return .{ .integer = value };
        return .{ .integer = declared };
    }

    /// What a switch expression yields: the union of the ranges of the
    /// arms, never the one arm a particular discriminant would pick.
    ///
    /// Nothing here knows which arm runs — the discriminant is a value
    /// this evaluator has not read — so every arm may be the one taken,
    /// and the answer has to hold for all of them.  That is also the
    /// safe direction when an arm cannot be read: `Range.join` answers
    /// `unknown` when either side is, and an unreadable arm keeps the
    /// declared type the arms share instead of being dropped, so a
    /// switch never claims a range narrower than its least readable arm
    /// allows.
    ///
    /// Each arm spends one step of the budget every other descent here
    /// shares, and the arms are siblings rather than nested, so a wide
    /// switch costs steps instead of the depth the walk reports.
    fn switchExpression(self: *Evaluator, node: Ast.Node.Index) Range {
        const switch_node = self.tree.fullSwitch(node) orelse return self.typeRange(node);
        var joined: ?Range = null;
        for (switch_node.ast.cases) |case_node| {
            const case = self.tree.fullSwitchCase(case_node) orelse return self.typeRange(node);
            // Captures bind arm-local values which incoming path facts do not
            // describe. Leave them to the declared result until modeled.
            if (case.payload_token != null) return self.typeRange(node);
            if (self.tree.nodeTag(ungroup(self.tree, case.ast.target_expr)) == .unreachable_literal) continue;
            const arm = self.evaluate(case.ast.target_expr);
            joined = if (joined) |left| left.join(arm) else arm;
        }
        // A switch that yields nothing, or one whose arms do not all
        // read, says exactly what reading none of them said: the type
        // they share.  That is the same bound the arms carried before
        // this arm existed, so a switch the evaluator cannot reduce
        // costs no precision.
        const value = joined orelse return self.typeRange(node);
        if (value == .unknown) return self.typeRange(node);
        // The arms are peer-typed with the switch itself, so the
        // declared type bounds the union from outside the same way it
        // bounds an integer arithmetic result.
        const declared = self.typeRange(node);
        if (declared == .integer and value == .integer) return value.intersect(declared);
        return value;
    }

    /// A plain field/identifier condition reads no code that can invalidate the
    /// incoming facts. Both returning arms must fit; no claim is made about
    /// which arm executes. More complex conditions retain the declared domain.
    fn conditionalExpression(self: *Evaluator, node: Ast.Node.Index) Range {
        const conditional = self.tree.fullIf(node) orelse return self.typeRange(node);
        if (conditional.payload_token != null) return self.typeRange(node);
        const condition = ungroup(self.tree, conditional.ast.cond_expr);
        if (path(self.tree, condition) == null) return self.typeRange(node);
        const fallback = conditional.ast.else_expr.unwrap() orelse return self.typeRange(node);
        const yes = ungroup(self.tree, conditional.ast.then_expr);
        const no = ungroup(self.tree, fallback);
        if (self.tree.nodeTag(yes) == .unreachable_literal) return self.evaluate(no);
        if (self.tree.nodeTag(no) == .unreachable_literal) return self.evaluate(yes);
        const joined = self.evaluate(yes).join(self.evaluate(no));
        if (joined == .unknown) return self.typeRange(node);
        const declared = self.typeRange(node);
        return if (joined == .integer and declared == .integer) joined.intersect(declared) else joined;
    }

    fn bitwise(self: *Evaluator, node: Ast.Node.Index) Range {
        const parts = self.tree.nodeData(node).node_and_node;
        const left = self.evaluate(parts[0]);
        const right = self.evaluate(parts[1]);
        const tag = self.tree.nodeTag(node);
        if (tag == .bit_and) {
            if (right == .integer and right.integer.min >= 0) return .{ .integer = .{
                .min = 0,
                .max = if (left == .integer and left.integer.min >= 0)
                    @min(left.integer.max, right.integer.max)
                else
                    right.integer.max,
            } };
            if (left == .integer and left.integer.min >= 0)
                return .{ .integer = .{ .min = 0, .max = left.integer.max } };
        }
        if (left != .integer or right != .integer or left.integer.min < 0 or right.integer.min < 0)
            return self.typeRange(node);
        const largest: u128 = @intCast(@max(left.integer.max, right.integer.max));
        const upper: i128 = if (largest == 0) 0 else @intCast(@as(u128, std.math.maxInt(u128)) >> @intCast(@clz(largest)));
        return .{ .integer = .{
            .min = if (tag == .bit_or) @max(left.integer.min, right.integer.min) else 0,
            .max = upper,
        } };
    }

    fn shift(self: *Evaluator, node: Ast.Node.Index) Range {
        const parts = self.tree.nodeData(node).node_and_node;
        const left = self.evaluate(parts[0]);
        const right = self.evaluate(parts[1]);
        if (left != .integer or right != .integer or right.integer.min < 0 or right.integer.max > 126)
            return self.typeRange(node);
        var low: i128 = std.math.maxInt(i128);
        var high: i128 = std.math.minInt(i128);
        for ([_]i128{ left.integer.min, left.integer.max }) |value| {
            for ([_]i128{ right.integer.min, right.integer.max }) |count| {
                const amount: u7 = @intCast(count);
                const shifted = if (self.tree.nodeTag(node) == .shr) value >> amount else std.math.mul(i128, value, @as(i128, 1) << amount) catch return self.typeRange(node);
                low = @min(low, shifted);
                high = @max(high, shifted);
            }
        }
        if (self.tree.nodeTag(node) == .shl) {
            const destination = self.typeRange(node);
            if (destination == .integer) {
                if (low < destination.integer.min or high > destination.integer.max) return destination;
            } else if (self.tree.nodeTag(parts[0]) != .number_literal or self.tree.nodeTag(parts[1]) != .number_literal)
                return .unknown;
        }
        return .{ .integer = .{ .min = low, .max = high } };
    }

    fn builtinCall(self: *Evaluator, node: Ast.Node.Index) Range {
        var buffer: [2]Ast.Node.Index = undefined;
        const params = self.tree.builtinCallParams(&buffer, node) orelse return .unknown;
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        if (params.len == 1 and std.mem.eql(u8, name, "@sizeOf")) {
            if (self.cache) |cache| {
                if (cache.comptimeIntValueOf(node)) |size| return Range.constant(size);
            }
            return self.typeRange(node);
        }
        if (std.mem.eql(u8, name, "@as") and params.len == 2)
            return self.coerce(self.evaluate(params[1]), params[1], params[0]);
        if (params.len == 1 and (std.mem.eql(u8, name, "@intCast") or std.mem.eql(u8, name, "@floatCast")))
            return self.coerce(self.evaluate(params[0]), params[0], node);
        if (params.len == 1 and std.mem.eql(u8, name, "@floatFromInt"))
            return self.evaluate(params[0]).asFloat(self.floatBits(node) orelse 0);
        if (params.len == 1 and std.mem.eql(u8, name, "@intFromEnum")) {
            const resolver = (self.cache orelse return self.typeRange(node)).zls orelse return self.typeRange(node);
            const tags = (resolver.enumIntegerRange(params[0]) catch return self.typeRange(node)) orelse return self.typeRange(node);
            return .{ .integer = .{ .min = tags.min, .max = tags.max } };
        }
        if (params.len == 2 and (std.mem.eql(u8, name, "@min") or std.mem.eql(u8, name, "@max")))
            return self.minimumMaximum(node, params[0], params[1], std.mem.eql(u8, name, "@min"));
        if (params.len == 2 and std.mem.eql(u8, name, "@divTrunc"))
            return self.evaluate(params[0]).binary(self.evaluate(params[1]), .div);
        if (params.len == 2 and std.mem.eql(u8, name, "@mod")) {
            const dividend = self.evaluate(params[0]);
            const divisor = self.evaluate(params[1]);
            if (dividend == .floating and divisor == .floating and
                dividend.floating.no_nan and divisor.floating.no_nan and
                std.math.isFinite(dividend.floating.min) and std.math.isFinite(dividend.floating.max) and
                std.math.isFinite(divisor.floating.min) and std.math.isFinite(divisor.floating.max) and
                divisor.floating.min > 0)
            {
                // A finite dividend modulo a finite positive divisor is
                // nonnegative. Keep the divisor endpoint inclusive: floating
                // rounding can produce the divisor itself.
                return (Range{ .floating = .{
                    .min = 0,
                    .max = divisor.floating.max,
                    .no_nan = true,
                } }).asFloat(self.floatBits(node) orelse 0);
            }
            return self.typeRange(node);
        }
        if (params.len == 1 and (std.mem.eql(u8, name, "@clz") or std.mem.eql(u8, name, "@ctz") or
            std.mem.eql(u8, name, "@popCount")))
        {
            if (self.cache) |cache| {
                if (cache.intInfoOf(params[0])) |info| return .{ .integer = .{ .min = 0, .max = info.bits } };
            }
        }
        if (params.len == 1) return self.floatBuiltin(node, name, params[0]);
        return self.typeRange(node);
    }

    fn minimumMaximum(self: *Evaluator, node: Ast.Node.Index, left: Ast.Node.Index, right: Ast.Node.Index, minimum: bool) Range {
        var a = self.evaluate(left);
        var b = self.evaluate(right);
        if (a == .unknown or b == .unknown or a == .floating or b == .floating) {
            const bits = self.floatBits(node) orelse return .unknown;
            a = a.asFloat(bits);
            b = b.asFloat(bits);
        }
        return a.binary(b, if (minimum) .minimum else .maximum);
    }

    fn floatBuiltin(self: *Evaluator, node: Ast.Node.Index, name: []const u8, operand: Ast.Node.Index) Range {
        const value = self.evaluate(operand);
        if (value != .floating) return self.typeRange(node);
        var result = value.floating;
        result.min_open = false;
        result.max_open = false;
        if (std.mem.eql(u8, name, "@abs")) {
            const lower = @abs(result.min);
            const upper = @abs(result.max);
            result.min = if (result.min <= 0 and result.max >= 0) 0 else @min(lower, upper);
            result.max = @max(lower, upper);
        } else if (std.mem.eql(u8, name, "@sqrt")) {
            result.no_nan = result.no_nan and result.min >= 0;
            result.min = std.math.nextAfter(f128, @sqrt(@max(result.min, 0)), -std.math.inf(f128));
            result.max = std.math.nextAfter(f128, @sqrt(@max(result.max, 0)), std.math.inf(f128));
        } else if (std.mem.eql(u8, name, "@floor")) {
            result.min = @floor(result.min);
            result.max = @floor(result.max);
        } else if (std.mem.eql(u8, name, "@ceil")) {
            result.min = @ceil(result.min);
            result.max = @ceil(result.max);
        } else if (std.mem.eql(u8, name, "@trunc")) {
            result.min = @trunc(result.min);
            result.max = @trunc(result.max);
        } else if (std.mem.eql(u8, name, "@round")) {
            result.min = @round(result.min);
            result.max = @round(result.max);
        } else return self.typeRange(node);
        return (Range{ .floating = result }).asFloat(self.floatBits(node) orelse 128);
    }

    fn standardCall(self: *Evaluator, node: Ast.Node.Index) Range {
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, node).?;
        const params = call.ast.params;
        if (params.len == 1) {
            if (self.constantFloatCall(node, params[0])) |value| return value;
        }
        if (params.len == 2) {
            if (self.integerLogarithmCall(node, params[0])) |value| return value;
        }
        if (!self.std_valid) return self.typeRange(node);
        const name = path(self.tree, call.ast.fn_expr) orelse return self.typeRange(node);
        if (params.len == 1 and std.mem.eql(u8, name, "std.math.inf"))
            return Range.floatConstant(std.math.inf(f128));
        if (params.len == 1 and std.mem.eql(u8, name, "std.math.nan")) return .{ .floating = .{} };
        if (params.len == 1 and (std.mem.eql(u8, name, "std.math.minInt") or std.mem.eql(u8, name, "std.math.maxInt"))) {
            const target = self.typeRange(params[0]);
            if (target != .integer) return .unknown;
            return Range.constant(if (std.mem.eql(u8, name, "std.math.minInt")) target.integer.min else target.integer.max);
        }
        if (params.len == 3 and std.mem.eql(u8, name, "std.math.clamp")) {
            const bits = self.floatBits(node) orelse return .unknown;
            const value = self.evaluate(params[0]).asFloat(bits);
            const lower = self.evaluate(params[1]).asFloat(bits);
            const upper = self.evaluate(params[2]).asFloat(bits);
            return value.binary(upper, .minimum).binary(lower, .maximum);
        }
        return self.typeRange(node);
    }

    /// Integer logarithms return at most the unsigned input type's bit width.
    /// Match the toolchain declaration, not a project helper with this name.
    fn integerLogarithmCall(self: *Evaluator, node: Ast.Node.Index, type_node: Ast.Node.Index) ?Range {
        const cache = self.cache orelse return null;
        const resolver = cache.zls orelse return null;
        const info = cache.intInfoOf(type_node) orelse return null;
        if (info.signed or info.bits == 0) return null;
        const reference = switch (resolver.functionReferenceOfCall(node) catch |err| return self.failedQuery(err)) {
            .function => |resolved| resolved,
            else => return null,
        };
        const function = reference.actual_type.data.function;
        if (!std.mem.eql(u8, function.name orelse return null, "log2_int_ceil")) return null;
        if (!(resolver.declaredInToolchainFile(reference.handle, "/std/math.zig") catch |err| return self.failedQuery(err)))
            return null;
        return .{ .integer = .{ .min = 0, .max = info.bits } };
    }

    fn failedQuery(self: *Evaluator, err: anyerror) ?Range {
        const SummaryError = @import("../cache/file_cache.zig").SummaryError;
        inline for (@typeInfo(SummaryError).error_set.?) |member| {
            const query_error = @field(SummaryError, member.name);
            if (err == query_error) {
                if (self.query_error) |record| record.* = record.* orelse query_error;
                return null;
            }
        }
        return null;
    }

    /// The backend instantiates a generic call's return TYPE, not its value.
    /// Certify the actual pure bit-construction body before supplying that
    /// missing constant. Neither a float type nor a function name proves a
    /// finite value: runtime f16 inputs still include NaN and infinity.
    fn constantFloatCall(self: *Evaluator, node: Ast.Node.Index, argument: Ast.Node.Index) ?Range {
        const resolver = (self.cache orelse return null).zls orelse return null;
        const frame = self.resolution_frame orelse resolver.resolutionFrame();
        const argument_value = (frame.resolveValueOfNode(argument) catch return null) orelse return null;
        if (!argument_value.is_type_val) return null;
        const bits = (frame.floatBits(argument) catch return null) orelse return null;
        const value: f128 = switch (bits) {
            16 => std.math.floatMax(f16),
            32 => std.math.floatMax(f32),
            64 => std.math.floatMax(f64),
            80 => std.math.floatMax(f80),
            128 => std.math.floatMax(f128),
            else => return null,
        };
        const reference = switch (resolver.functionReferenceOfCall(node) catch return null) {
            .function => |resolved| resolved,
            else => return null,
        };
        const function = reference.actual_type.data.function;
        if (!std.mem.eql(u8, function.name orelse return null, "floatMax")) return null;
        if (!(resolver.declaredInToolchainFile(reference.handle, "/std/math/float.zig") catch return null))
            return null;
        if (!self.floatMaximumBody(reference.tree, reference.fn_token)) return null;
        return Range.floatConstant(value);
    }

    /// The closed primitive chain computes the all-ones mantissa, the largest
    /// finite exponent, and their unsigned bit representation. Check every
    /// signature and body; a changed primitive or extra statement withdraws
    /// the proof. Token comparison ignores only whitespace and line comments.
    fn floatMaximumBody(self: *Evaluator, tree: *const Ast, reached_token: Ast.TokenIndex) bool {
        var found: [float_maximum_primitives.len]bool = @splat(false);
        for (tree.rootDecls()) |declaration| {
            if (self.budget.* == 0) {
                self.noteStop(.numeric_oracle_steps, self.budget_cap);
                return false;
            }
            self.budget.* -= 1;
            if (tree.nodeTag(declaration) != .fn_decl) continue;
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, declaration) orelse continue;
            const name = tree.tokenSlice(proto.name_token orelse continue);
            for (float_maximum_primitives, 0..) |primitive, index| {
                if (!std.mem.eql(u8, name, primitive.name)) continue;
                if (found[index]) return false;
                if (index == 0 and proto.ast.fn_token != reached_token) return false;
                if (!self.matchesPrimitive(tree, proto.ast.fn_token, tree.lastToken(declaration), primitive.source))
                    return false;
                found[index] = true;
            }
        }
        for (found) |present| if (!present) return false;
        return true;
    }

    fn matchesPrimitive(
        self: *Evaluator,
        tree: *const Ast,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        expected: [:0]const u8,
    ) bool {
        var tokenizer = std.zig.Tokenizer.init(expected);
        var actual = first;
        while (actual <= last) : (actual += 1) {
            if (self.budget.* == 0) {
                self.noteStop(.numeric_oracle_steps, self.budget_cap);
                return false;
            }
            self.budget.* -= 1;
            const token = tokenizer.next();
            if (token.tag != tree.tokenTag(actual)) return false;
            if (!std.mem.eql(u8, tree.tokenSlice(actual), expected[token.loc.start..token.loc.end])) return false;
        }
        return tokenizer.next().tag == .eof;
    }
};

/// Source-level semantics of the supported SDK primitive, not an exemption
/// keyed by pathname. All five bodies must still be present in the resolved
/// toolchain declaration's document before its concrete type argument yields
/// a constant. A new SDK implementation stays unknown until it is understood.
const float_maximum_primitives = [_]struct { name: []const u8, source: [:0]const u8 }{
    .{
        .name = "floatMax",
        .source =
        \\fn floatMax(comptime T: type) T {
        \\    const all1s_mantissa = (1 << floatMantissaBits(T)) - 1;
        \\    return reconstructFloat(T, floatExponentMax(T), all1s_mantissa);
        \\}
        ,
    },
    .{
        .name = "reconstructFloat",
        .source =
        \\fn reconstructFloat(comptime T: type, comptime exponent: comptime_int, comptime mantissa: comptime_int) T {
        \\    const TBits = @Int(.unsigned, @bitSizeOf(T));
        \\    const biased_exponent = @as(TBits, exponent + floatExponentMax(T));
        \\    return @as(T, @bitCast((biased_exponent << floatMantissaBits(T)) | @as(TBits, mantissa)));
        \\}
        ,
    },
    .{
        .name = "floatExponentMax",
        .source =
        \\fn floatExponentMax(comptime T: type) comptime_int {
        \\    return (1 << (floatExponentBits(T) - 1)) - 1;
        \\}
        ,
    },
    .{
        .name = "floatExponentBits",
        .source =
        \\fn floatExponentBits(comptime T: type) comptime_int {
        \\    comptime assert(@typeInfo(T) == .float);
        \\    return switch (@typeInfo(T).float.bits) {
        \\        16 => 5,
        \\        32 => 8,
        \\        64 => 11,
        \\        80 => 15,
        \\        128 => 15,
        \\        else => @compileError("unknown floating point type " ++ @typeName(T)),
        \\    };
        \\}
        ,
    },
    .{
        .name = "floatMantissaBits",
        .source =
        \\fn floatMantissaBits(comptime T: type) comptime_int {
        \\    comptime assert(@typeInfo(T) == .float);
        \\    return switch (@typeInfo(T).float.bits) {
        \\        16 => 10,
        \\        32 => 23,
        \\        64 => 52,
        \\        80 => 64,
        \\        128 => 112,
        \\        else => @compileError("unknown floating point type " ++ @typeName(T)),
        \\    };
        \\}
        ,
    },
};

/// Wrappers one path peel may undo before it declines.
///
/// A peel is SYNTACTIC, not a descent: it only unwraps `(…)`, `.field` and
/// `.*`, and each of those steps strictly shortens the token span, so it cannot
/// loop and it consumes no step.  The cap is therefore not a walk-depth bound
/// and must not be reported as one — it is the same NUMBER the module spends on
/// a real descent (`Evaluator.frame_cap`) so this file has one depth in it
/// rather than two spellings of it, and a peel that reaches the cap gives the
/// same answer a peel that found no identifier gives: null, which proves
/// nothing.  Nothing that was provable before stops being provable.
const max_path_peel: usize = Evaluator.frame_cap;

pub fn path(tree: *const Ast, original: Ast.Node.Index) ?[]const u8 {
    const node = ungroup(tree, original);
    var part = node;
    for (0..max_path_peel) |_| {
        switch (tree.nodeTag(part)) {
            .identifier => {
                const first = tree.firstToken(node);
                const last = tree.lastToken(node);
                return tree.source[tree.tokenStart(first) .. tree.tokenStart(last) + tree.tokenSlice(last).len];
            },
            .field_access => part = tree.nodeData(part).node_and_token[0],
            .deref => part = tree.nodeData(part).node,
            .grouped_expression => part = tree.nodeData(part).node_and_token[0],
            else => return null,
        }
    }
    return null;
}

fn ungroup(tree: *const Ast, original: Ast.Node.Index) Ast.Node.Index {
    var node = original;
    for (0..max_path_peel) |_| {
        if (tree.nodeTag(node) != .grouped_expression) return node;
        node = tree.nodeData(node).node_and_token[0];
    }
    return node;
}

pub const Constraint = struct { node: Ast.Node.Index, value: Range };

/// What a std math finiteness predicate adds to the value it is handed: a
/// proven `std.math.isFinite(x)` also rules out an infinite bound, a proven
/// `std.math.isNan(x)` being false rules out NaN alone.
pub const Finiteness = enum { finite, not_nan };

/// The nodes `refine` records a fact under, in recording order; `count == 0`
/// means it records nothing for that condition.
///
/// A caller that has to NAME what a proved condition left behind has to be
/// reading the set the recording writes under, so `refine` reads this rather
/// than the other way round — one switch is the only place that can say so.
/// Both shapes are here: a comparison records under each of its OPERANDS, and
/// a call-shaped finiteness predicate under the argument it was handed.
pub const Targets = struct {
    nodes: [2]Ast.Node.Index = undefined,
    count: u2 = 0,
    /// Read only when `count == 1`, the call shape.
    finiteness: Finiteness = .not_nan,

    pub const none: Targets = .{ .count = 0 };

    pub fn slice(self: *const Targets) []const Ast.Node.Index {
        return self.nodes[0..self.count];
    }
};

/// The std math predicates `refine` records a finiteness fact for, and what
/// each records.  The polarity matters: `isFinite` says something only when it
/// holds, `isNan` only when it does not.
fn finitenessOf(name: []const u8, truth: bool) ?Finiteness {
    if (std.mem.eql(u8, name, "std.math.isFinite")) return if (truth) .finite else null;
    if (std.mem.eql(u8, name, "std.math.isNan")) return if (truth) null else .not_nan;
    return null;
}

pub fn recordedTargets(
    evaluation: *Evaluator,
    original: Ast.Node.Index,
    truth: bool,
) Targets {
    const tree = evaluation.tree;
    return targetsAt(tree, ungroup(tree, original), evaluation.std_valid, truth);
}

fn targetsAt(tree: *const Ast, node: Ast.Node.Index, std_valid: bool, truth: bool) Targets {
    var call_buffer: [1]Ast.Node.Index = undefined;
    if (tree.fullCall(&call_buffer, node)) |call| {
        if (!std_valid or call.ast.params.len != 1) return .none;
        const finiteness = finitenessOf(path(tree, call.ast.fn_expr) orelse return .none, truth) orelse
            return .none;
        return .{ .nodes = .{ call.ast.params[0], undefined }, .count = 1, .finiteness = finiteness };
    }
    if (comparison(tree.nodeTag(node), truth) == null) return .none;
    return .{ .nodes = tree.nodeData(node).node_and_node, .count = 2 };
}

pub fn refine(evaluation: *Evaluator, original: Ast.Node.Index, truth: bool) [2]?Constraint {
    const tree = evaluation.tree;
    const node = ungroup(tree, original);
    const tag = tree.nodeTag(node);
    const targets = targetsAt(tree, node, evaluation.std_valid, truth);
    if (targets.count == 0) return .{ null, null };
    // A finiteness predicate records under the one value it was handed.
    if (targets.count == 1) {
        var value = evaluation.evaluate(targets.nodes[0]);
        if (value != .floating) value = .{ .floating = .{} };
        value.floating.no_nan = true;
        if (targets.finiteness == .finite) {
            if (std.math.isInf(value.floating.min)) value.floating.min_open = true;
            if (std.math.isInf(value.floating.max)) value.floating.max_open = true;
        }
        return .{ .{ .node = targets.nodes[0], .value = value }, null };
    }
    const op = comparison(tag, truth) orelse return .{ null, null };
    const parts = tree.nodeData(node).node_and_node;
    const left = evaluation.evaluate(parts[0]);
    const right = evaluation.evaluate(parts[1]);
    if (path(tree, parts[0])) |key| {
        if (path(tree, parts[1])) |other| {
            if (std.mem.eql(u8, key, other) and
                ((tag == .equal_equal and truth) or (tag == .bang_equal and !truth)))
            {
                var value = left;
                if (value == .unknown) value = .{ .floating = .{} };
                if (value == .floating) value.floating.no_nan = true;
                return .{ .{ .node = parts[0], .value = value }, null };
            }
        }
    }
    return .{
        .{ .node = parts[0], .value = constrained(evaluation, parts[0], left, right, op, tag, truth) },
        .{ .node = parts[1], .value = constrained(evaluation, parts[1], right, left, reverse(op), tag, truth) },
    };
}

const Comparison = enum { lt, le, gt, ge, eq, ne };

fn comparison(tag: Ast.Node.Tag, truth: bool) ?Comparison {
    return switch (tag) {
        .less_than => if (truth) .lt else .ge,
        .less_or_equal => if (truth) .le else .gt,
        .greater_than => if (truth) .gt else .le,
        .greater_or_equal => if (truth) .ge else .lt,
        .equal_equal => if (truth) .eq else .ne,
        .bang_equal => if (truth) .ne else .eq,
        else => null,
    };
}

fn reverse(op: Comparison) Comparison {
    return switch (op) {
        .lt => .gt,
        .le => .ge,
        .gt => .lt,
        .ge => .le,
        .eq => .eq,
        .ne => .ne,
    };
}

fn constrained(
    evaluation: *Evaluator,
    node: Ast.Node.Index,
    value: Range,
    limit: Range,
    op: Comparison,
    tag: Ast.Node.Tag,
    truth: bool,
) Range {
    if (value == .integer and limit == .integer) return constrainInteger(value.integer, limit.integer, op);
    const current = if (value == .floating)
        value.floating
    else
        evaluation.floatEnvelope(value, node, null).floating;
    const boundary = evaluation.floatEnvelope(limit, node, null).floating;
    const ordered = (truth and tag != .bang_equal) or (!truth and tag == .bang_equal);
    return constrainFloat(current, boundary, op, ordered);
}

fn constrainInteger(original: numbers.Integer, limit: numbers.Integer, op: Comparison) Range {
    var value = original;
    switch (op) {
        .lt => value.max = @min(value.max, std.math.sub(i128, limit.max, 1) catch return .unknown),
        .le => value.max = @min(value.max, limit.max),
        .gt => value.min = @max(value.min, std.math.add(i128, limit.min, 1) catch return .unknown),
        .ge => value.min = @max(value.min, limit.min),
        .eq => {
            value.min = @max(value.min, limit.min);
            value.max = @min(value.max, limit.max);
        },
        .ne => if (limit.min == limit.max) {
            if (value.min == limit.min) value.min = std.math.add(i128, value.min, 1) catch return .unknown;
            if (value.max == limit.max) value.max = std.math.sub(i128, value.max, 1) catch return .unknown;
        },
    }
    if (value.min > value.max) return .unknown;
    return .{ .integer = value };
}

fn constrainFloat(original: numbers.Floating, limit: numbers.Floating, op: Comparison, ordered: bool) Range {
    if (!ordered and !limit.no_nan) return .{ .floating = original };
    var value = original;
    if (ordered) value.no_nan = true;
    switch (op) {
        .lt, .le => {
            if (limit.max <= value.max) {
                const open = (op == .lt) or limit.max_open;
                value.max_open = open or (limit.max == value.max and value.max_open);
                value.max = limit.max;
            }
        },
        .gt, .ge => {
            if (limit.min >= value.min) {
                const open = (op == .gt) or limit.min_open;
                value.min_open = open or (limit.min == value.min and value.min_open);
                value.min = limit.min;
            }
        },
        .eq => return (Range{ .floating = value }).intersect(.{ .floating = limit }),
        .ne => if (limit.min == limit.max and limit.no_nan) {
            if (value.min == limit.min) value.min_open = true;
            if (value.max == limit.max) value.max_open = true;
        },
    }
    if (value.min > value.max) return .unknown;
    return .{ .floating = value };
}

// ── Tests ────────────────────────────────────────────────────────
// These drive the evaluator with no type cache, so what they pin is the
// switch dispatch itself: the union of the arms, the prong that catches
// the rest, and an arm that cannot be read taking the answer with it.

/// The range of the first switch expression in `source`, evaluated with
/// no type cache: every arm the fixtures write is either a literal or a
/// name only a cache could resolve, so nothing here but the arms
/// decides the answer.
fn switchRange(gpa: std.mem.Allocator, source: [:0]const u8) !Range {
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .@"switch" or tag == .switch_comma) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.NoSwitch;
    var budget: u32 = Evaluator.frame_cap;
    var evaluation: Evaluator = .{
        .tree = &tree,
        .cache = null,
        .facts = &.{},
        .budget = &budget,
        .std_valid = true,
    };
    return evaluation.evaluate(node);
}

fn integerOf(value: Range) error{NotAnInteger}!numbers.Integer {
    return switch (value) {
        .integer => |bounds| bounds,
        else => error.NotAnInteger,
    };
}

test "a switch expression reads as the union of every arm" {
    const gpa = std.testing.allocator;
    const source = try gpa.dupeZ(u8,
        \\const Format = enum { half, single, double };
        \\fn biasOf(format: Format) i32 {
        \\    return switch (format) {
        \\        .half => 15,
        \\        .single => 127,
        \\        .double => 1023,
        \\    };
        \\}
    );
    defer gpa.free(source);
    // Every arm may be the one that runs: no discriminant has been read,
    // so the range spans all three and neither end of the type does.
    try std.testing.expectEqual(
        numbers.Integer{ .min = 15, .max = 1023 },
        try integerOf(try switchRange(gpa, source)),
    );
}

test "a switch expression keeps the prong that catches the rest" {
    const gpa = std.testing.allocator;
    const source = try gpa.dupeZ(u8,
        \\fn scale(large: bool) i32 {
        \\    return switch (large) {
        \\        true => 1,
        \\        else => 1000,
        \\    };
        \\}
    );
    defer gpa.free(source);
    // The catch-all runs whenever no tagged prong does, so answering with
    // the tagged arm alone would be narrower than the switch really is.
    try std.testing.expectEqual(
        numbers.Integer{ .min = 1, .max = 1000 },
        try integerOf(try switchRange(gpa, source)),
    );
}

test "a switch expression does not drop an arm it cannot read" {
    const gpa = std.testing.allocator;
    const source = try gpa.dupeZ(u8,
        \\const Format = enum { half, single, double };
        \\const Spec = struct { bias: i32 };
        \\fn biasOf(format: Format, spec: *const Spec) i32 {
        \\    return switch (format) {
        \\        .half => 15,
        \\        .single => spec.bias,
        \\        .double => 1023,
        \\    };
        \\}
    );
    defer gpa.free(source);
    // `spec.bias` is a field only the cache could resolve.  Joining the
    // two readable arms and skipping it would answer `[15, 1023]` for a
    // switch that can also yield whatever the caller put in the struct.
    try std.testing.expect((try switchRange(gpa, source)) == .unknown);
}

test "embedded extent query failures retain the owning walk's first error" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "const bytes = @embedFile(\"data.bin\");", .zig);
    defer tree.deinit(gpa);
    const initializer = tree.fullVarDecl(tree.rootDecls()[0]).?.ast.init_node.unwrap().?;
    for ([_]?@import("../cache/file_cache.zig").SummaryError{ null, error.Canceled }) |earlier| {
        var failing = std.testing.FailingAllocator.init(gpa, .{ .fail_index = 0 });
        var cache = FileCache.init(failing.allocator(), &tree);
        defer cache.deinit();
        var query_error = earlier;
        var budget: u32 = 100;
        var evaluation: Evaluator = .{
            .tree = &tree,
            .cache = &cache,
            .facts = &.{},
            .budget = &budget,
            .std_valid = false,
            .query_error = &query_error,
        };
        try std.testing.expect(evaluation.containerLength(initializer) == .unknown);
        try std.testing.expectEqual(earlier orelse error.OutOfMemory, query_error.?);
    }
}

fn descriptorLengthRange(source: [:0]const u8) !Range {
    const gpa = std.testing.allocator;
    const engine = @import("type_engine");
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "Op.zig",
        .data =
        \\const std = @import("std");
        \\pub const Op = enum(u16) { first, second, third };
        \\pub const descriptors: [std.meta.fields(Op).len]u8 = .{ 1, 2, 3 };
        ,
    });
    const root = try tmp.dir.realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(root);
    const file_path = try std.fs.path.join(gpa, &.{ root, "caller.zig" });
    defer gpa.free(file_path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, file_path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var budget: u32 = 1000;
    var query_error: ?@import("../cache/file_cache.zig").SummaryError = null;
    var evaluation: Evaluator = .{
        .tree = tree,
        .cache = &cache,
        .facts = &.{},
        .budget = &budget,
        .std_valid = true,
        .container_consts = .{ .tree = tree, .cache = &cache, .walk_binds = &.{} },
        .query_error = &query_error,
    };
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"return") continue;
        const value = tree.nodeData(@enumFromInt(index)).opt_node.unwrap() orelse continue;
        const result = evaluation.evaluate(value);
        if (query_error) |err| return err;
        return result;
    }
    return error.NoReturn;
}

test "descriptor extent uses the exact enum owner's constant array literal" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Op = enum(u16) {
        \\    first, second, third,
        \\    const descriptors: [std.meta.fields(@This()).len]u8 = .{ 1, 2, 3 };
        \\};
        \\fn length() usize { return Op.descriptors.len; }
    ;
    try std.testing.expectEqual(
        numbers.Integer{ .min = 3, .max = 3 },
        try integerOf(try descriptorLengthRange(source)),
    );
}

test "descriptor extent keeps root and nested known literals exact" {
    const fixtures = [_][:0]const u8{
        \\const std = @import("std");
        \\const Op = enum(u16) { first, second, third };
        \\const descriptors: [std.meta.fields(Op).len]u8 = .{ 1, 2, 3 };
        \\fn length() usize { return descriptors.len; }
        ,
        \\const std = @import("std");
        \\const Module = struct {
        \\    const Op = enum(u16) { first, second, third };
        \\    const descriptors: [std.meta.fields(Op).len]u8 = .{ 1, 2, 3 };
        \\};
        \\fn length() usize { return Module.descriptors.len; }
        ,
        \\const Table = struct { const values = [_]u8{ 1, 2, 3 }; };
        \\fn length() usize { return Table.values.len; }
        ,
    };
    for (fixtures) |source| {
        try std.testing.expectEqual(
            numbers.Integer{ .min = 3, .max = 3 },
            try integerOf(try descriptorLengthRange(source)),
        );
    }
}

test "descriptor extent does not borrow an opaque or shadowed owner's literal" {
    const fixtures = [_][:0]const u8{
        \\const Op = struct { const descriptors = [_]u8{ 1, 2, 3 }; };
        \\fn length(Op: anytype) usize { return Op.descriptors.len; }
        ,
        \\const Op = struct { var descriptors: []const u8 = &.{ 1, 2, 3 }; };
        \\fn length() usize { return Op.descriptors.len; }
        ,
        \\const Op = struct { extern const descriptors: []const u8; };
        \\fn length() usize { return Op.descriptors.len; }
        ,
        \\const Op = struct { const descriptors: []const u8 = opaqueDescriptors(); };
        \\fn length() usize { return Op.descriptors.len; }
        ,
        \\const ExternalOp = @import("unresolved-enum-module");
        \\const Op = struct {
        \\    const descriptors: [@import("std").meta.fields(ExternalOp).len]u8 = undefined;
        \\};
        \\fn length() usize { return Op.descriptors.len; }
        ,
    };
    for (fixtures) |source| {
        const result = try descriptorLengthRange(source);
        if (result == .integer) try std.testing.expect(result.integer.max > 65535);
    }
}

test "descriptor extent follows the exact imported module's known literal" {
    const source: [:0]const u8 =
        \\const Op = @import("Op.zig");
        \\fn length() usize { return Op.descriptors.len; }
    ;
    try std.testing.expectEqual(
        numbers.Integer{ .min = 3, .max = 3 },
        try integerOf(try descriptorLengthRange(source)),
    );
}

test "constant extent allocation failures retain the owning walk's first error" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "const values = [_]u8{ 1, 2, 3 }; fn length() usize { return values.len; }", .zig);
    defer tree.deinit(gpa);
    const value = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(@enumFromInt(index))), "values"))
            break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.NoValues;
    for ([_]?@import("../cache/file_cache.zig").SummaryError{ null, error.Canceled }) |earlier| {
        var failing = std.testing.FailingAllocator.init(gpa, .{ .fail_index = 0 });
        var cache = FileCache.init(failing.allocator(), &tree);
        defer cache.deinit();
        var query_error = earlier;
        var budget: u32 = 100;
        var evaluation: Evaluator = .{
            .tree = &tree,
            .cache = &cache,
            .facts = &.{},
            .budget = &budget,
            .std_valid = false,
            .container_consts = .{ .tree = &tree, .cache = &cache, .walk_binds = &.{} },
            .query_error = &query_error,
        };
        try std.testing.expect(evaluation.containerLength(value) == .unknown);
        try std.testing.expectEqual(earlier orelse error.OutOfMemory, query_error.?);
    }
}
