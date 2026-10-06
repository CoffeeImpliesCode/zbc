//! Per-file semantic model.
//!
//! Built ONCE per `Ast` (typically per file).  Rules ask the model
//! questions instead of re-walking the token stream to answer them:
//!
//!   - "Does this file declare a struct named `Outer`?"
//!     → `model.findType(\"Outer\")`
//!   - "Does `Outer` have a method called `deinit`?"
//!     → `outer.hasMethod(\"deinit\")` or `outer.findMethod(\"deinit\")`
//!   - "What fields does `Outer` have?  What are their types?"
//!     → `outer.fields`
//!   - "What top-level fns exist?  Which are methods of which type?"
//!     → `model.fns`, each with `enclosing_type`
//!
//! Three rules currently re-build a private version of this every
//! call: `missing_deinit_on_composed_owner` (struct-deinit table),
//! `asymmetric_field_free` (struct-field+free-pair table), and
//! `reset_skips_pooled_resource_release` (struct + method body
//! ranges).  After this lands they share one cache.
//!
//! Approach: token-level scan, NOT a recursive Ast.Node walk.  Why:
//!   - The four `container_decl*` AST tag variants are awkward to
//!     dispatch over; token-walking sidesteps them.
//!   - All current rules already token-walk; the model matches
//!     their idiom so they keep using `TokenIndex` for spans.
//!   - The "find struct decl + walk its body" pattern is well-
//!     tested across the existing rules; we're just centralizing it.
//!
//! Scope (v1):
//!   - Top-level `const Name = struct/union/enum { ... }` decls
//!   - Methods inside those decls
//!   - Fields inside structs (best-effort, identifier `: type,` shape)
//!   - Top-level `fn name(...)` decls (NOT methods — those live in
//!     types[].methods)
//!
//! Out of scope (v1):
//!   - Nested types (struct inside struct).  Add when a rule needs it.
//!   - Anonymous types (`return struct { ... }`).  Add when needed.
//!   - extern fns / extern structs.
//!   - Inheritance via `usingnamespace` (deprecated anyway).

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");
const method_names = @import("method_names.zig");

pub const TokenIndex = tokens.TokenIndex;
const TokenTag = tokens.TokenTag;

pub const TypeKind = enum { struct_, union_, enum_, opaque_ };

pub const FieldInfo = struct {
    /// The field's identifier slice (borrowed from `tree`).
    name: []const u8,
    /// Token index of the identifier.
    name_token: TokenIndex,
    /// First token of the type expression (after `:`).
    type_first: TokenIndex,
    /// Last token of the type expression (before `=` default or `,`).
    type_last: TokenIndex,
    /// True if the field has a `= <default>` initializer.
    has_default: bool,
};

pub const Receiver = struct {
    /// Parameter name — usually "self", "this", but could be
    /// anything (e.g. "inspector").
    name: []const u8,
    name_token: TokenIndex,
    /// True if the receiver is `*Self` / `*Name` (vs `Self` / `Name`).
    is_ptr: bool,
    /// True if `*const Self` (only meaningful when `is_ptr`).
    is_const: bool,
};

pub const MethodInfo = struct {
    /// Method name (borrowed from `tree`).
    name: []const u8,
    name_token: TokenIndex,
    /// The fn_decl AST node.
    fn_decl: Ast.Node.Index,
    /// The body AST node (block_*).
    body: Ast.Node.Index,
    /// First token of the body (`{`).
    body_first: TokenIndex,
    /// Last token of the body (`}`).
    body_last: TokenIndex,
    /// True if declared `pub fn ...`.
    is_pub: bool,
    /// The first parameter, if it looks like a method receiver
    /// (named `self`/`this` OR typed as `Self`/`*Self`/the
    /// enclosing type name).  null for "static" methods.
    receiver: ?Receiver,
};

pub const TypeInfo = struct {
    /// Type's declared name (`const Name = struct { ... }` → "Name").
    name: []const u8,
    qualified_name: []const u8,
    /// Token index of the name (the `Name` identifier).
    name_token: TokenIndex,
    /// struct / union / enum / opaque.
    kind: TypeKind,
    /// Token index of the body's opening `{`.
    body_first: TokenIndex,
    /// Token index of the body's closing `}`.
    body_last: TokenIndex,
    /// All struct-level fields (best-effort identifier-colon detection).
    /// Empty for enum / opaque.
    fields: []const FieldInfo,
    /// All `fn name(...)` declarations inside the body.
    methods: []const MethodInfo,
    /// Index into FileModel.types of the enclosing type, if this is
    /// a nested type declaration (`const Outer = struct { const Inner
    /// = struct { ... }; };`).  null for top-level types.
    parent: ?u32 = null,

    pub fn hasMethod(self: TypeInfo, name: []const u8) bool {
        return self.findMethod(name) != null;
    }

    pub fn findMethod(self: TypeInfo, name: []const u8) ?*const MethodInfo {
        for (self.methods) |*m| {
            if (std.mem.eql(u8, m.name, name)) return m;
        }
        return null;
    }

    /// True iff the type has any cleanup method (deinit/close/
    /// destroy/free/stop/finalize/dispose) — the canonical
    /// "this type owns something that needs releasing" signal.
    fn hasCleanupMethod(self: TypeInfo) bool {
        for (self.methods) |m| {
            if (method_names.isCleanupMethodName(m.name)) return true;
        }
        return false;
    }

    pub fn findField(self: TypeInfo, name: []const u8) ?*const FieldInfo {
        for (self.fields) |*f| {
            if (std.mem.eql(u8, f.name, name)) return f;
        }
        return null;
    }
};

pub const FnInfo = struct {
    name: []const u8,
    name_token: TokenIndex,
    fn_decl: Ast.Node.Index,
    body: Ast.Node.Index,
    body_first: TokenIndex,
    body_last: TokenIndex,
    is_pub: bool,
    returns_error_union: bool,
};

pub const FileModel = struct {
    /// All allocations live here.  `deinit` drops everything at once.
    arena: std.heap.ArenaAllocator,
    tree: *const Ast,
    /// All top-level struct/union/enum declarations.
    types: []const TypeInfo,
    /// All top-level fn_decl nodes.  Methods live in `types[].methods`,
    /// NOT here.
    fns: []const FnInfo,

    pub fn deinit(self: *FileModel) void {
        self.arena.deinit();
    }

    /// True iff the file declares `const <type_name> = @This();` at
    /// the top level — the file-struct pattern where the file
    /// itself IS the type, and file-level fns are its methods.
    /// Common in Bun (e.g. `ReadableStream.zig` starts with
    /// `const ReadableStream = @This();`).
    pub fn fileIsTypeNamed(self: *const FileModel, type_name: []const u8) bool {
        const tags = self.tree.tokens.items(.tag);
        var t: TokenIndex = 0;
        // Scan the first few top-level decls; the @This() alias is
        // conventionally near the file head.
        var scanned: u32 = 0;
        while (t + 4 < self.tree.tokens.len and scanned < 64) : (t += 1) {
            if (tags[t] != .keyword_const) continue;
            scanned += 1;
            if (tags[t + 1] != .identifier) continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t + 1), type_name)) continue;
            if (tags[t + 2] != .equal) continue;
            if (tags[t + 3] != .builtin) continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t + 3), "@This")) continue;
            return true;
        }
        return false;
    }

    /// True iff `<type_name>` has a method (or file-level fn, when
    /// the file is a `@This()`-aliased file-struct) named `method`.
    /// Composes `typeHasMethod` with the file-struct fallback.
    pub fn typeOrFileHasMethod(self: *const FileModel, type_name: []const u8, method: []const u8) bool {
        if (self.findType(type_name)) |ti| {
            if (ti.hasMethod(method)) return true;
        }
        if (self.fileIsTypeNamed(type_name)) {
            for (self.fns) |f| {
                if (std.mem.eql(u8, f.name, method)) return true;
            }
        }
        return false;
    }

    /// Find a type by name (linear scan; types lists are small per file).
    pub fn findType(self: *const FileModel, name: []const u8) ?*const TypeInfo {
        for (self.types) |*t| {
            if (std.mem.eql(u8, t.qualified_name, name)) return t;
        }
        return null;
    }

    /// Scope-aware type lookup.  Find `name` starting from
    /// `start_ti`'s scope (sibling types in the same parent), then
    /// walk OUTWARD through ancestor scopes, falling back to a
    /// file-level scan.  Resolves the canonical
    /// "outer.Inner.Outer.Inner" collision where a field in
    /// `Pending: ... { future: Future }` should resolve to the
    /// `Future` declared in the SAME enclosing scope as `Pending`
    /// rather than an unrelated like-named type elsewhere in the
    /// file.
    pub fn findTypeInScope(self: *const FileModel, name: []const u8, start_ti: *const TypeInfo) ?*const TypeInfo {
        // Compute `start_ti`'s INDEX in the types array — used to
        // search its own NESTED types (children) before walking
        // outward.  A field's type can reference a type DECLARED
        // INSIDE its own owner (e.g. `Pending { future: Future,
        // pub const Future = ... }`), so the first hop is into
        // ct_ti itself.
        var start_idx: ?u32 = null;
        for (self.types, 0..) |*t, i| {
            if (t == start_ti) {
                start_idx = @intCast(i);
                break;
            }
        }
        // First pass: children of `start_ti`.
        if (start_idx) |idx| {
            for (self.types) |*t| {
                if (t.parent != idx) continue;
                if (std.mem.eql(u8, t.name, name)) return t;
            }
        }
        // Walk outward through ancestor scopes.  At each level
        // search the types whose parent matches the current scope.
        var scope_parent: ?u32 = start_ti.parent;
        while (true) {
            for (self.types) |*t| {
                if (t.parent != scope_parent) continue;
                if (std.mem.eql(u8, t.name, name)) return t;
            }
            // Move to outer scope.
            const parent_idx = scope_parent orelse break;
            if (parent_idx >= self.types.len) break;
            scope_parent = self.types[parent_idx].parent;
        }
        return null;
    }

    /// Resolve a qualified type path like `["Result", "Pending", "State"]`
    /// to the EXACT nested type, disambiguating against name collisions.
    /// `findType` returns the first match (often the wrong one); this
    /// follows the parent chain to find the nested type with the right
    /// enclosing scope.
    ///
    /// Matching strategy: scan all types whose NAME matches the LAST
    /// segment; for each candidate, walk its `parent` chain upward and
    /// verify the chain's names match the path's earlier segments
    /// (right-to-left).  Returns the first candidate whose chain
    /// matches.
    pub fn findQualifiedType(
        self: *const FileModel,
        path: []const []const u8,
    ) ?*const TypeInfo {
        if (path.len == 0) return null;
        if (path.len == 1) return self.findType(path[0]);
        const leaf_name = path[path.len - 1];
        for (self.types) |*candidate| {
            if (!std.mem.eql(u8, candidate.name, leaf_name)) continue;
            if (self.qualifiedChainMatches(candidate, path)) return candidate;
        }
        return null;
    }

    /// True iff `ti`'s parent chain (walking outward) matches the
    /// names in `path[0..path.len-1]` in reverse order.
    fn qualifiedChainMatches(
        self: *const FileModel,
        ti: *const TypeInfo,
        path: []const []const u8,
    ) bool {
        if (path.len < 2) return true;
        // Walk from `ti`'s parent upward.  path[len-2] should match
        // the immediate parent, path[len-3] the grandparent, etc.
        var i: usize = path.len - 1;
        var cur: ?u32 = ti.parent;
        while (i > 0) {
            i -= 1;
            const parent_idx = cur orelse return false;
            // Defensive bounds check: in pathological cases (e.g. an
            // arena reused across builds or a model snapshot taken
            // mid-construction) a parent index might exceed the
            // final slice length.  ReleaseSafe would panic; we
            // prefer a graceful "no match" so the call site falls
            // back to the first-identifier heuristic.
            if (parent_idx >= self.types.len) return false;
            const parent_ti = &self.types[parent_idx];
            if (!std.mem.eql(u8, parent_ti.name, path[i])) return false;
            cur = parent_ti.parent;
        }
        return cur == null;
    }

    /// Resolve a field's full type-path (`Result.Pending.State`) to
    /// the nested TypeInfo.  Walks the field's declared type tokens,
    /// strips wrappers (`*` / `?` / `[]`), collects each identifier
    /// in the dotted chain, then calls `findQualifiedType`.  Returns
    /// null when the path can't be resolved (cross-file, generic
    /// instantiation, etc.).
    pub fn resolveFieldTypeQualified(
        self: *const FileModel,
        struct_name: []const u8,
        field_name: []const u8,
    ) ?*const TypeInfo {
        const ti = self.findType(struct_name) orelse return null;
        return self.resolveFieldTypeQualifiedTi(ti, field_name);
    }

    /// TypeInfo-anchored variant of `resolveFieldTypeQualified`.
    /// Bypasses the name-keyed lookup that would land on the wrong
    /// nested-type collision when callers already hold a precise
    /// outer type pointer.
    pub fn resolveFieldTypeQualifiedTi(
        self: *const FileModel,
        ti: *const TypeInfo,
        field_name: []const u8,
    ) ?*const TypeInfo {
        const field = ti.findField(field_name) orelse return null;
        const name = tokens.typeNameFromTokens(self.tree, field.type_first, field.type_last) orelse return null;
        return self.resolveTypeNameInScope(name, ti);
    }

    pub fn resolveTypeNameInScope(self: *const FileModel, name: []const u8, owner: *const TypeInfo) ?*const TypeInfo {
        var segments = std.mem.splitScalar(u8, name, '.');
        const first = std.mem.trim(u8, segments.next() orelse return null, &std.ascii.whitespace);
        var current = self.findTypeInScope(first, owner) orelse return null;
        var depth: u8 = 0;
        while (segments.next()) |part| : (depth += 1) {
            if (depth == 32) return null;
            const segment = std.mem.trim(u8, part, &std.ascii.whitespace);
            current = child: {
                for (self.types) |*candidate| {
                    const parent = candidate.parent orelse continue;
                    if (&self.types[parent] != current) continue;
                    if (std.mem.eql(u8, candidate.name, segment)) break :child candidate;
                }
                return null;
            };
        }
        return current;
    }

    /// Convenience: type exists AND has the named method.
    pub fn typeHasMethod(self: *const FileModel, type_name: []const u8, method_name: []const u8) bool {
        const ti = self.findType(type_name) orelse return false;
        return ti.hasMethod(method_name);
    }

    /// Find a top-level fn by name.
    pub fn findFn(self: *const FileModel, name: []const u8) ?*const FnInfo {
        for (self.fns) |*f| {
            if (std.mem.eql(u8, f.name, name)) return f;
        }
        return null;
    }

    /// True iff the file declares a type with this name.
    pub fn hasType(self: *const FileModel, name: []const u8) bool {
        return self.findType(name) != null;
    }

    /// Find the type whose body contains `fn_decl`.  Returns null
    /// for top-level fns.  When `fn_decl` is inside a nested type,
    /// returns the INNERMOST enclosing type (smallest body range),
    /// not the outer — methods on nested types should associate
    /// with their declaring type, not its container.
    pub fn containingTypeOf(self: *const FileModel, fn_decl: Ast.Node.Index) ?*const TypeInfo {
        return self.containingTypeAtToken(self.tree.firstToken(fn_decl));
    }

    pub fn containingTypeAtToken(self: *const FileModel, fn_tok: TokenIndex) ?*const TypeInfo {
        var best: ?*const TypeInfo = null;
        var best_span: u32 = std.math.maxInt(u32);
        for (self.types) |*ti| {
            if (fn_tok > ti.body_first and fn_tok < ti.body_last) {
                const span = ti.body_last - ti.body_first;
                if (span < best_span) {
                    best = ti;
                    best_span = span;
                }
            }
        }
        return best;
    }

    /// Complete declared name after pointer/optional qualifiers.
    /// Arrays, slices, function types, and unresolved shapes return null.
    pub fn fieldType(self: *const FileModel, struct_name: []const u8, field_name: []const u8) ?[]const u8 {
        const ti = self.findType(struct_name) orelse return null;
        const f = ti.findField(field_name) orelse return null;
        return tokens.typeNameFromTokens(self.tree, f.type_first, f.type_last);
    }


    /// True iff the field's declared type starts with `*` (after
    /// stripping `?` / `const`).  Heuristic for "this field is a
    /// borrow, not an owned value" — pointer-typed struct fields
    /// almost always alias storage that lives elsewhere.
    pub fn fieldIsPointer(self: *const FileModel, struct_name: []const u8, field_name: []const u8) bool {
        const ti = self.findType(struct_name) orelse return false;
        const f = ti.findField(field_name) orelse return false;
        const tags = self.tree.tokens.items(.tag);
        var t: TokenIndex = f.type_first;
        while (t <= f.type_last) : (t += 1) {
            switch (tags[t]) {
                .question_mark, .keyword_const => {},
                .asterisk => return true,
                else => return false,
            }
        }
        return false;
    }

    /// True iff the field is declared `<field>: ?T = null` — an
    /// optional with the null default.  The first non-null write to
    /// such a field is initializing it, not overwriting a prior
    /// owned value — the overwrite-without-deinit rule should not
    /// fire on the lazy-init pattern (e.g. `attachSignal` setting
    /// `this.signal` for the first time).
    pub fn fieldIsOptionalNullDefault(
        self: *const FileModel,
        struct_name: []const u8,
        field_name: []const u8,
    ) bool {
        const ti = self.findType(struct_name) orelse return false;
        const f = ti.findField(field_name) orelse return false;
        if (!f.has_default) return false;
        const tags = self.tree.tokens.items(.tag);
        // Type must begin with `?` to qualify as optional.
        if (tags[f.type_first] != .question_mark) return false;
        // Locate the `=` after `type_last`; default value's first
        // token sits at `=` + 1.
        var eq: TokenIndex = f.type_last + 1;
        while (eq < self.tree.tokens.len and tags[eq] != .equal) : (eq += 1) {}
        if (eq >= self.tree.tokens.len) return false;
        const dv = eq + 1;
        if (dv >= self.tree.tokens.len) return false;
        if (tags[dv] != .identifier) return false;
        return std.mem.eql(u8, self.tree.tokenSlice(dv), "null");
    }

    /// True iff `<struct_name>.<field_name>`'s declared default value
    /// is `.{}` — an empty struct literal.  Such a default is the
    /// type's all-fields-default form; if all of the type's own
    /// fields default to non-owning values (the canonical case for
    /// types with `field: T = .{}` shape), dropping a default
    /// instance can't leak anything.  Conservative: this check
    /// only confirms the LITERAL is `.{}` — the caller is
    /// responsible for further checks if it wants to confirm the
    /// type's defaults are themselves non-owning.
    pub fn fieldDefaultIsEmptyStructLiteral(
        self: *const FileModel,
        struct_name: []const u8,
        field_name: []const u8,
    ) bool {
        const ti = self.findType(struct_name) orelse return false;
        const f = ti.findField(field_name) orelse return false;
        if (!f.has_default) return false;
        const tags = self.tree.tokens.items(.tag);
        var eq: TokenIndex = f.type_last + 1;
        while (eq < self.tree.tokens.len and tags[eq] != .equal) : (eq += 1) {}
        if (eq + 2 >= self.tree.tokens.len) return false;
        // `.{}` is tokens: `.` `{` `}`.
        return tags[eq + 1] == .period and
            tags[eq + 2] == .l_brace and
            (eq + 3 < self.tree.tokens.len and tags[eq + 3] == .r_brace);
    }

    /// Whether `<struct_name>.<field_name>`'s default value is a
    /// tagged-union variant whose payload is NON-OWNED — a bare
    /// tag like `.pending` (no payload) or `.empty`.  Returns the
    /// tag name (e.g. "pending") on match, null otherwise.  Used
    /// by the union-variant-aware overwrite check to recognise
    /// "first write transitions from a known empty initial tag".
    pub fn fieldDefaultUnionTag(
        self: *const FileModel,
        struct_name: []const u8,
        field_name: []const u8,
    ) ?[]const u8 {
        const ti = self.findType(struct_name) orelse return null;
        const f = ti.findField(field_name) orelse return null;
        if (!f.has_default) return null;
        const tags = self.tree.tokens.items(.tag);
        var eq: TokenIndex = f.type_last + 1;
        while (eq < self.tree.tokens.len and tags[eq] != .equal) : (eq += 1) {}
        if (eq >= self.tree.tokens.len) return null;
        const dv = eq + 1;
        if (dv + 1 >= self.tree.tokens.len) return null;
        // Bare tag: `. <ident>` not followed by `{` / `(` / `.`.
        if (tags[dv] == .period and tags[dv + 1] == .identifier) {
            const next = dv + 2;
            if (next < self.tree.tokens.len) {
                switch (tags[next]) {
                    .l_brace, .l_paren, .period => {},
                    else => return self.tree.tokenSlice(dv + 1),
                }
            } else {
                return self.tree.tokenSlice(dv + 1);
            }
        }
        // Struct-init form: `. { . <tag> = ... }`.
        if (dv + 3 < self.tree.tokens.len and
            tags[dv] == .period and
            tags[dv + 1] == .l_brace and
            tags[dv + 2] == .period and
            tags[dv + 3] == .identifier)
        {
            return self.tree.tokenSlice(dv + 3);
        }
        return null;
    }

    /// True iff `type_name` is declared as a tagged union — any
    /// `union(<TagType>) {...}` form (`union(enum)` is the most
    /// common; `union(MyTag)` is also accepted).  Plain
    /// `union {...}` (untagged) doesn't qualify.
    pub fn isTaggedUnion(self: *const FileModel, type_name: []const u8) bool {
        const ti = self.findType(type_name) orelse return false;
        if (ti.kind != .union_) return false;
        const tags = self.tree.tokens.items(.tag);
        // body_first is the `{`; walk back to find `union`.
        var t: TokenIndex = ti.body_first;
        while (t > 0) {
            t -= 1;
            if (tags[t] == .keyword_union) break;
        }
        // After `union` we want `(` ... `)` (tag-type in between).
        // Most common: `(enum)` or `(MyTag)`.  Any non-empty
        // parenthesised tag-type counts as tagged.
        if (t + 2 >= self.tree.tokens.len) return false;
        if (tags[t + 1] != .l_paren) return false;
        // Walk to matching `)`; depth-1 means at least one token
        // (the tag type) sits inside.
        var u: TokenIndex = t + 2;
        var depth: i32 = 1;
        while (u < self.tree.tokens.len and depth > 0) : (u += 1) {
            switch (tags[u]) {
                .l_paren => depth += 1,
                .r_paren => depth -= 1,
                else => {},
            }
        }
        // Empty `()` is invalid syntax; assume non-empty parens
        // mean a tag type.
        return depth == 0 and u > t + 3;
    }

    /// Owned-ness of a tagged-union variant: true iff the variant
    /// has a payload type that itself has a `deinit` method (i.e.
    /// the payload is OWNED storage).  Variants with no payload
    /// (`.pending,`) or primitive payloads (`u32`/`bool`) are
    /// considered non-owned — overwriting them never leaks.
    ///
    /// Returns `null` if the tag isn't a variant of this type.
    pub fn unionVariantIsOwned(
        self: *const FileModel,
        union_name: []const u8,
        variant_tag: []const u8,
    ) ?bool {
        const ti = self.findType(union_name) orelse return null;
        return self.unionVariantIsOwnedTi(ti, variant_tag);
    }

    /// Variant of `unionVariantIsOwned` that takes the resolved
    /// `TypeInfo` directly — used when the caller has already
    /// disambiguated a qualified path (e.g. `Result.Pending.State`)
    /// and doesn't want a `findType` re-lookup to grab the wrong
    /// like-named type.
    pub fn unionVariantIsOwnedTi(
        self: *const FileModel,
        ti: *const TypeInfo,
        variant_tag: []const u8,
    ) ?bool {
        if (ti.kind != .union_) return null;
        const tags = self.tree.tokens.items(.tag);
        var t: TokenIndex = ti.body_first + 1;
        const last = ti.body_last;
        while (t < last) : (t += 1) {
            // Variant starts at an identifier at depth 0 of the
            // union body (skip past method decls / nested types).
            if (tags[t] == .keyword_fn or tags[t] == .keyword_pub or
                tags[t] == .keyword_const or tags[t] == .keyword_var) {
                // Skip the entire decl (method/const/etc.) — walk
                // to its terminating `;` or end-of-block `}` at
                // depth 0.
                t = skipDeclStmt(tags, t, last);
                continue;
            }
            if (tags[t] != .identifier) continue;
            const name = self.tree.tokenSlice(t);
            // Variant payload form: `<tag>: <type>,` or `<tag>,`.
            // Skip if the next non-identifier-tail token is `=` /
            // `.` (a `const X = …;` we didn't catch above) or `(`
            // (a `pub fn …(` past the keyword_pub strip we lost).
            const after = t + 1;
            if (after >= last) break;
            if (tags[after] == .comma) {
                if (std.mem.eql(u8, name, variant_tag)) return false;
                continue;
            }
            if (tags[after] == .colon) {
                // Payload follows; parse its base type identifier.
                if (std.mem.eql(u8, name, variant_tag)) {
                    return self.payloadIsOwned(tags, after + 1, last);
                }
                // Skip to the next comma at depth 0.
                t = skipToTopComma(tags, after + 1, last);
                continue;
            }
            // Some other shape — give up on this iter.
        }
        return null;
    }

    fn payloadIsOwned(
        self: *const FileModel,
        tags: []const TokenTag,
        start: TokenIndex,
        last: TokenIndex,
    ) bool {
        // Anonymous-struct payload (`struct { ... }`): walk its
        // fields and treat as non-owned only if every field is a
        // pointer or primitive.  A pointer field is a BORROW; a
        // primitive field is a value — neither leaks on drop.
        if (start < last and tags[start] == .keyword_struct) {
            return anonStructHasOwnedField(self, tags, start, last);
        }
        // Walk type tokens; collect the last identifier (the base
        // type name).  Stop at the next top-level comma.
        var t: TokenIndex = start;
        var last_id: ?[]const u8 = null;
        var paren_depth: i32 = 0;
        while (t < last) : (t += 1) {
            switch (tags[t]) {
                .l_paren, .l_bracket => paren_depth += 1,
                .r_paren, .r_bracket => paren_depth -= 1,
                .comma => if (paren_depth == 0) break,
                .identifier => last_id = self.tree.tokenSlice(t),
                else => {},
            }
        }
        const name = last_id orelse return false;
        // Primitive types: never owned.
        if (isPrimitiveBaseName(name)) return false;
        // Pointer/optional payloads: assume owned (`*T` / `?*T` /
        // `?T` where T has deinit).  Cheap conservative call —
        // the rule's purpose is to find leaks, so when in doubt
        // treat as owned.
        if (self.findType(name)) |payload_ti| {
            return payload_ti.hasMethod("deinit") or
                payload_ti.hasMethod("deref") or
                payload_ti.hasMethod("destroy") or
                payload_ti.hasMethod("close");
        }
        // Unknown type — assume owned (conservative; cross-file
        // resolution could refine).
        return true;
    }

    /// True iff `struct_name`.`field_name` is the heap-owning half of
    /// a flag-paired ownership pattern: a sibling field
    /// `<field_name>_allocated: bool` exists on the same struct.
    /// Inference-equivalent of the old `Db.flag_owned_fields` set —
    /// pure syntactic pairing, no annotation needed.
    fn isFlagOwnedField(self: *const FileModel, struct_name: []const u8, field_name: []const u8) bool {
        const ti = self.findType(struct_name) orelse return false;
        if (ti.findField(field_name) == null) return false;
        // Look for the sibling `<field>_allocated: bool` field.
        var buf: [128]u8 = undefined;
        const suffix = "_allocated";
        if (field_name.len + suffix.len > buf.len) return false;
        @memcpy(buf[0..field_name.len], field_name);
        @memcpy(buf[field_name.len..][0..suffix.len], suffix);
        const sibling_name = buf[0 .. field_name.len + suffix.len];
        const sibling = ti.findField(sibling_name) orelse return false;
        // Sibling type must be exactly `bool`.
        if (sibling.type_first != sibling.type_last) return false;
        return std.mem.eql(u8, self.tree.tokenSlice(sibling.type_first), "bool");
    }

    /// Iterate over `(field_name)` pairs of every flag-owned field
    /// on `struct_name`.  Caller-owned slice; freed by `gpa.free`.
    pub fn flagOwnedFields(
        self: *const FileModel,
        gpa: std.mem.Allocator,
        struct_name: []const u8,
    ) ![]const []const u8 {
        const ti = self.findType(struct_name) orelse return &.{};
        var out: std.ArrayListUnmanaged([]const u8) = .empty;
        for (ti.fields) |f| {
            if (self.isFlagOwnedField(struct_name, f.name)) {
                try out.append(gpa, f.name);
            }
        }
        return out.toOwnedSlice(gpa);
    }
};

/// True iff `name_tok` is nested inside ANY `fn ... { ... }` body
/// in the source — even one enclosing nested struct/union/enum
/// decls.  Walks backward through every unmatched `{`; at each one,
/// looks back for the keyword that opens the brace (`fn` -> fn body,
/// `struct`/`union`/`enum` -> type body).  Returns true on the
/// first `fn` brace found, false if we reach the file top without
/// hitting one.
///
/// Used to filter out methods of structs returned from generic fns
/// (e.g. `fn Wrap(T) type { return struct { fn deinit(...) {} }; }`)
/// from model.fns — those bodies live inside a fn's source range
/// and would otherwise look top-level by syntactic walk.
fn isInsideFnBody(tree: *const Ast, name_tok: TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (name_tok == 0) return false;
    var t: i64 = @as(i64, @intCast(name_tok)) - 1;
    var depth: i32 = 0;
    while (t >= 0) : (t -= 1) {
        const tok: TokenIndex = @intCast(t);
        switch (tags[tok]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    // Unmatched `{`.  Identify what opened it.
                    switch (braceOpenerKind(tags, tok)) {
                        .fn_body => return true,
                        .type_body => {
                            // Struct/union/enum body — continue
                            // walking outward past it.  depth stays
                            // 0 (we're now in the enclosing scope).
                        },
                        .unknown => return false,
                    }
                } else {
                    depth -= 1;
                }
            },
            else => {},
        }
    }
    return false;
}

const BraceOpener = enum { fn_body, type_body, unknown };

/// Classify what kind of construct opens the `{` at `brace_tok`.
/// Looks back past parens/type-expressions for the introducing
/// keyword.  Conservative: returns `.unknown` rather than guessing
/// when the lookback hits a terminator or runs out of budget.
fn braceOpenerKind(tags: []const std.zig.Token.Tag, brace_tok: TokenIndex) BraceOpener {
    if (brace_tok == 0) return .unknown;
    var u: i64 = @as(i64, @intCast(brace_tok)) - 1;
    var paren: i32 = 0;
    var hops: u32 = 0;
    while (u >= 0 and hops < 128) : ({
        u -= 1;
        hops += 1;
    }) {
        const ut: TokenIndex = @intCast(u);
        switch (tags[ut]) {
            .r_paren => paren += 1,
            .l_paren => paren -= 1,
            .keyword_fn => if (paren == 0) return .fn_body,
            .keyword_struct, .keyword_union, .keyword_enum, .keyword_opaque => {
                if (paren == 0) return .type_body;
            },
            // Block / stmt terminators break the lookback.
            .l_brace, .r_brace, .semicolon => if (paren == 0) return .unknown,
            else => {},
        }
    }
    return .unknown;
}


/// Build a FileModel for the given Ast.  `tree` must outlive the model.
pub fn build(gpa: std.mem.Allocator, tree: *const Ast) !FileModel {
    return buildWithPath(gpa, tree, null);
}

/// Like `build` but also infers a file-as-struct name from the
/// filename's stem when the source uses the bun convention
/// (`pub const new = bun.TrivialNew(@This())` / `bun.New(@This())` /
/// `RefCount(@This(), ...)`) without an explicit `const X = @This();`.
/// Pass `file_path` (absolute or relative — only the basename is
/// used) so cross-file lookups can resolve types named after their
/// containing file.
pub fn buildWithPath(gpa: std.mem.Allocator, tree: *const Ast, file_path: ?[]const u8) !FileModel {
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const a = arena.allocator();

    var types: std.ArrayListUnmanaged(TypeInfo) = .empty;
    var fns: std.ArrayListUnmanaged(FnInfo) = .empty;

    const tags = tree.tokens.items(.tag);
    const tok_count: u32 = @intCast(tree.tokens.len);
    if (tok_count == 0) {
        return .{
            .arena = arena,
            .tree = tree,
            .types = &.{},
            .fns = &.{},
        };
    }
    const last: TokenIndex = tok_count - 1;

    // ── Pass 1: top-level type decls ───────────────────────
    // Walks file tokens for `[pub] const Name = struct/union/enum {
    // ... };` at brace-depth 0; recurses into each collected type's
    // body to pick up nested type declarations (`const Inner = struct
    // { ... }` inside an outer struct's body).  Nested entries land in
    // the same flat `types` list with `parent` set to the outer's
    // index.
    try collectTypesInRange(a, tree, &types, 0, last, null);

    // ── Pass 2: top-level fn decls ─────────────────────────
    // Walk Ast.fn_decl nodes; classify as top-level by checking that
    // their containing token is NOT inside any type body we just
    // collected.
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buf, node) orelse continue;
        const name_tok = proto.name_token orelse continue;
        const body = tokens.bodyOf(tree, node) orelse continue;

        // Skip if inside a type body.
        var inside_type = false;
        for (types.items) |ti| {
            if (name_tok > ti.body_first and name_tok < ti.body_last) {
                inside_type = true;
                break;
            }
        }
        if (inside_type) continue;

        // Skip if inside ANY fn's body (i.e., this is a nested fn /
        // a method on a struct declared inside `fn X() type { return
        // struct { ... }; }`).  Without this filter, methods of
        // generic-fn-returned structs leak into model.fns as
        // pseudo-top-level entries — summaryByName then finds them
        // and applies their inferred takes to unrelated call sites.
        if (isInsideFnBody(tree, name_tok)) continue;

        try fns.append(a, .{
            .name = tree.tokenSlice(name_tok),
            .name_token = name_tok,
            .fn_decl = node,
            .body = body,
            .body_first = tree.firstToken(body),
            .body_last = tree.lastToken(body),
            .is_pub = isPrecededByPub(tags, name_tok),
            .returns_error_union = protoReturnsErrorUnion(tree, proto),
        });
    }

    // File-as-struct: if the file declares `const <Name> = @This();`
    // at top level, synthesize a TypeInfo for it with file-top-level
    // fields and methods (the file-level fn list).  Lets findType /
    // fieldType / etc. resolve fields and methods uniformly across
    // `const X = struct { ... }` and `const X = @This();` shapes.
    const inferred_name: ?[]const u8 = detectFileStructName(tree) orelse blk: {
        if (file_path) |fp| {
            if (fileLooksLikeStruct(tree)) {
                const base = std.fs.path.basename(fp);
                // Strip `.zig` suffix to get the stem.
                if (std.mem.endsWith(u8, base, ".zig") and base.len > 4) {
                    break :blk base[0 .. base.len - 4];
                }
            }
        }
        break :blk null;
    };
    if (inferred_name) |fs_name| {
        // Skip if a type with the same name was already collected
        // (defensive — shouldn't happen since file-struct decls don't
        // open a brace body and aren't picked up by collectTypesInRange).
        const dup = blk: {
            for (types.items) |ti| {
                if (std.mem.eql(u8, ti.name, fs_name)) break :blk true;
            }
            break :blk false;
        };
        if (!dup) {
            const fs_fields = try collectFields(a, tree, 0, last);
            // Convert file-level fns into method-shape entries.
            var fs_methods: std.ArrayListUnmanaged(MethodInfo) = .empty;
            for (fns.items) |f| {
                var proto_buf: [1]Ast.Node.Index = undefined;
                const proto = tokens.fnProto(tree, &proto_buf, f.fn_decl) orelse continue;
                try fs_methods.append(a, .{
                    .name = f.name,
                    .name_token = f.name_token,
                    .fn_decl = f.fn_decl,
                    .body = f.body,
                    .body_first = f.body_first,
                    .body_last = f.body_last,
                    .is_pub = f.is_pub,
                    .receiver = extractReceiver(tree, proto, fs_name),
                });
            }
            // Find the name token of the `@This()` decl as a stable
            // pos anchor (mirrors how collectTypesInRange records
            // name_token).
            const fs_name_tok = findFileStructNameToken(tree, fs_name) orelse 0;
            try types.append(a, .{
                .name = fs_name,
                .qualified_name = fs_name,
                .name_token = fs_name_tok,
                .kind = .struct_,
                .body_first = 0,
                .body_last = last,
                .fields = fs_fields,
                .methods = try fs_methods.toOwnedSlice(a),
                .parent = null,
            });
        }
    }

    return .{
        .arena = arena,
        .tree = tree,
        .types = try types.toOwnedSlice(a),
        .fns = try fns.toOwnedSlice(a),
    };
}

/// True iff the file's top-level syntax looks like a struct
/// definition: contains the bun convention `bun.TrivialNew(@This())`
/// / `bun.New(@This())` / `RefCount(@This(), ...)` mixin OR a
/// `pub fn <name>(<recv>: *@This())` method (recv typed as @This()
/// — strong signal of "file IS the struct").  Used by buildWithPath
/// to recover the implicit type name from the filename when the
/// source doesn't have a `const X = @This();` alias.
fn fileLooksLikeStruct(tree: *const Ast) bool {
    const tags = tree.tokens.items(.tag);
    const tok_count: u32 = @intCast(tree.tokens.len);
    // Scan for `<ident>(@This())` patterns or `*@This()` in fn
    // signatures.  Bound the scan to the first ~512 tokens for
    // performance — the convention places these markers near the
    // file head.
    var t: TokenIndex = 0;
    const scan_end: TokenIndex = if (tok_count < 1024) tok_count else 1024;
    while (t + 2 < scan_end) : (t += 1) {
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@This")) continue;
        // `@This()` — confirmed.  This appears in any of the bun
        // mixins (TrivialNew / New / RefCount) and in `*@This()`
        // method receivers; either signals file-struct usage.
        return true;
    }
    return false;
}

fn detectFileStructName(tree: *const Ast) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    const tok_count: u32 = @intCast(tree.tokens.len);
    var t: TokenIndex = 0;
    var scanned: u32 = 0;
    while (t + 4 < tok_count and scanned < 64) : (t += 1) {
        if (tags[t] != .keyword_const) continue;
        scanned += 1;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), "@This")) continue;
        return tree.tokenSlice(t + 1);
    }
    return null;
}

fn findFileStructNameToken(tree: *const Ast, name: []const u8) ?TokenIndex {
    const tags = tree.tokens.items(.tag);
    const tok_count: u32 = @intCast(tree.tokens.len);
    var t: TokenIndex = 0;
    var scanned: u32 = 0;
    while (t + 4 < tok_count and scanned < 64) : (t += 1) {
        if (tags[t] != .keyword_const) continue;
        scanned += 1;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), name)) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), "@This")) continue;
        return t + 1;
    }
    return null;
}

// ── Internal: type, field, method extraction ──────────────

/// Collect every `const Name = struct/union/enum/opaque { ... }`
/// decl in `[start, end]` at brace-depth 0 (relative to `start`),
/// then recurse into each collected type's body to pick up nested
/// type decls.  All collected types share the same flat `types`
/// list; nested entries carry `parent` = the index of the enclosing
/// type at append time.
fn collectTypesInRange(
    a: std.mem.Allocator,
    tree: *const Ast,
    types: *std.ArrayListUnmanaged(TypeInfo),
    start: TokenIndex,
    end: TokenIndex,
    parent: ?u32,
) std.mem.Allocator.Error!void {
    const tags = tree.tokens.items(.tag);
    if (end < 4 or start + 4 >= end) return;

    var depth: u32 = 0;
    var t: TokenIndex = start;
    while (t + 4 < end) : (t += 1) {
        switch (tags[t]) {
            .l_brace, .l_paren, .l_bracket => {
                depth += 1;
                continue;
            },
            .r_brace, .r_paren, .r_bracket => {
                if (depth > 0) depth -= 1;
                continue;
            },
            else => {},
        }
        if (depth != 0) continue;
        if (tags[t] != .keyword_const) continue;
        if (tags[t + 1] != .identifier) continue;
        var eq: TokenIndex = t + 2;
        while (eq < end and tags[eq] != .equal and tags[eq] != .semicolon) : (eq += 1) {}
        if (eq >= end or tags[eq] != .equal) continue;
        if (eq + 2 > end) continue;
        var k: TokenIndex = eq + 1;
        if (tags[k] == .keyword_extern or tags[k] == .keyword_packed) k += 1;
        if (k + 1 > end) continue;
        const kind: TypeKind = switch (tags[k]) {
            .keyword_struct => .struct_,
            .keyword_union => .union_,
            .keyword_enum => .enum_,
            .keyword_opaque => .opaque_,
            else => continue,
        };
        var b: TokenIndex = k + 1;
        if (b <= end and tags[b] == .l_paren) {
            const cp = tokens.matchParen(tags, b, end) orelse continue;
            b = cp + 1;
        }
        if (b > end or tags[b] != .l_brace) continue;
        const body_last = tokens.matchBrace(tags, b, end) orelse continue;

        const fields_slice = if (kind == .struct_ or kind == .union_)
            try collectFields(a, tree, b + 1, body_last - 1)
        else
            &[_]FieldInfo{};
        const methods_slice = try collectMethods(a, tree, b + 1, body_last - 1, tree.tokenSlice(t + 1));

        const this_index: u32 = @intCast(types.items.len);
        try types.append(a, .{
            .name = tree.tokenSlice(t + 1),
            .qualified_name = if (parent) |index|
                try std.fmt.allocPrint(a, "{s}.{s}", .{ types.items[index].qualified_name, tree.tokenSlice(t + 1) })
            else tree.tokenSlice(t + 1),
            .name_token = t + 1,
            .kind = kind,
            .body_first = b,
            .body_last = body_last,
            .fields = fields_slice,
            .methods = methods_slice,
            .parent = parent,
        });

        // Recurse into THIS type's body to collect any nested type
        // decls.  `b + 1` skips the opening `{`; `body_last - 1`
        // stops before the closing `}`.
        if (body_last > b + 1) {
            try collectTypesInRange(a, tree, types, b + 1, body_last - 1, this_index);
        }

        // Skip past the body so the outer scan doesn't re-enter it.
        t = body_last;
    }
}

/// True iff the anonymous struct payload starting at `start`
/// (the `struct` keyword) contains at least one OWNED field —
/// a non-pointer non-primitive whose type has a `deinit` (or
/// equivalent).  Returns false when every field is `*T` / `?*T`
/// (a borrow) or a primitive (a value) — no leak possible.
fn anonStructHasOwnedField(
    model: *const FileModel,
    tags: []const TokenTag,
    start: TokenIndex,
    last: TokenIndex,
) bool {
    if (start + 2 > last) return true;
    if (tags[start] != .keyword_struct) return true;
    if (tags[start + 1] != .l_brace) return true;
    var t: TokenIndex = start + 2;
    var depth: i32 = 1;
    while (t < last and depth > 0) {
        // A field starts with an identifier (the field name)
        // followed by `:` at brace depth 1.  Skip method / const
        // decls.
        switch (tags[t]) {
            .l_brace => {
                depth += 1;
                t += 1;
                continue;
            },
            .r_brace => {
                depth -= 1;
                t += 1;
                continue;
            },
            .keyword_fn, .keyword_pub, .keyword_const, .keyword_var => {
                t = skipDeclStmt(tags, t, last);
                t += 1;
                continue;
            },
            .identifier => {
                if (t + 1 < last and tags[t + 1] == .colon) {
                    // Field — parse type tokens.
                    const type_start = t + 2;
                    // Scan the type tokens up to the next `,` / `}`
                    // / default `=` at depth 1.
                    var u: TokenIndex = type_start;
                    var pd: i32 = 0;
                    while (u < last) : (u += 1) {
                        switch (tags[u]) {
                            .l_paren, .l_bracket, .l_brace => pd += 1,
                            .r_paren, .r_bracket, .r_brace => {
                                if (pd == 0) break;
                                pd -= 1;
                            },
                            .comma, .equal => if (pd == 0) break,
                            else => {},
                        }
                    }
                    // Field-type tokens are [type_start, u-1].
                    if (fieldTypeIsOwnedValue(model, tags, type_start, u)) return true;
                    t = u;
                    continue;
                }
                t += 1;
                continue;
            },
            else => {
                t += 1;
                continue;
            },
        }
    }
    return false;
}

/// True iff the type tokens `[start, end)` form an OWNED VALUE —
/// not a pointer (`*T` / `?*T`) and not a primitive.  Used by
/// `anonStructHasOwnedField` to classify each field of an
/// anonymous struct payload.
fn fieldTypeIsOwnedValue(
    model: *const FileModel,
    tags: []const TokenTag,
    start: TokenIndex,
    end: TokenIndex,
) bool {
    if (start >= end) return false;
    var t: TokenIndex = start;
    // Skip `?` qualifier; a `?*T` is still a pointer.
    while (t < end and tags[t] == .question_mark) : (t += 1) {}
    if (t < end and tags[t] == .asterisk) return false; // pointer
    if (t < end and tags[t] == .l_bracket) return false; // slice/array
    // Collect the last identifier as the base type.
    var last_id: ?[]const u8 = null;
    var pd: i32 = 0;
    while (t < end) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket => pd += 1,
            .r_paren, .r_bracket => pd -= 1,
            .identifier => last_id = model.tree.tokenSlice(t),
            else => {},
        }
    }
    const name = last_id orelse return false;
    if (isPrimitiveBaseName(name)) return false;
    if (model.findType(name)) |ti| {
        return ti.hasMethod("deinit") or
            ti.hasMethod("deref") or
            ti.hasMethod("destroy") or
            ti.hasMethod("close");
    }
    // Cross-file unknown — conservatively treat as owned.
    return true;
}

/// Token-walk past one top-level decl (`pub fn …`, `const X = …;`,
/// `var Y = …;`) inside a type body.  Used by union-variant scans
/// to step over method declarations between variants.  Returns the
/// position of the decl's terminating `}` (for fn bodies) or `;`.
fn skipDeclStmt(
    tags: []const TokenTag,
    start: TokenIndex,
    last: TokenIndex,
) TokenIndex {
    var t: TokenIndex = start;
    var brace_depth: i32 = 0;
    var paren_depth: i32 = 0;
    while (t < last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => brace_depth += 1,
            .r_brace => {
                brace_depth -= 1;
                if (brace_depth == 0 and paren_depth == 0) return t;
            },
            .l_paren => paren_depth += 1,
            .r_paren => paren_depth -= 1,
            .semicolon => if (brace_depth == 0 and paren_depth == 0) return t,
            else => {},
        }
    }
    return last;
}

/// Walk forward to the next comma at parenthesis/bracket depth 0.
/// Used by union-variant scans to step from one variant's payload
/// type to the next variant declaration.
fn skipToTopComma(
    tags: []const TokenTag,
    start: TokenIndex,
    last: TokenIndex,
) TokenIndex {
    var t: TokenIndex = start;
    var pd: i32 = 0;
    var bd: i32 = 0;
    while (t < last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket => pd += 1,
            .r_paren, .r_bracket => pd -= 1,
            .l_brace => bd += 1,
            .r_brace => bd -= 1,
            .comma => if (pd == 0 and bd == 0) return t,
            else => {},
        }
    }
    return last;
}

/// True iff `name` is a Zig primitive numeric / bool type.  Used
/// by union-variant payload-owned-ness inference: a variant with
/// a primitive payload can never leak.
fn isPrimitiveBaseName(name: []const u8) bool {
    if (std.mem.eql(u8, name, "bool")) return true;
    if (std.mem.eql(u8, name, "void")) return true;
    if (std.mem.eql(u8, name, "anyopaque")) return true;
    if (std.mem.eql(u8, name, "usize")) return true;
    if (std.mem.eql(u8, name, "isize")) return true;
    if (std.mem.eql(u8, name, "f16") or std.mem.eql(u8, name, "f32") or
        std.mem.eql(u8, name, "f64") or std.mem.eql(u8, name, "f80") or
        std.mem.eql(u8, name, "f128")) return true;
    if (name.len < 2) return false;
    const lead = name[0];
    if (lead != 'u' and lead != 'i') return false;
    for (name[1..]) |c| if (c < '0' or c > '9') return false;
    return true;
}

fn collectFields(
    a: std.mem.Allocator,
    tree: *const Ast,
    start: TokenIndex,
    end: TokenIndex,
) ![]const FieldInfo {
    var out: std.ArrayListUnmanaged(FieldInfo) = .empty;
    const tags = tree.tokens.items(.tag);
    if (start > end) return try out.toOwnedSlice(a);

    var t: TokenIndex = start;
    while (t <= end) : (t += 1) {
        // Skip nested braces (fn bodies, anon struct types).
        if (tags[t] == .l_brace) {
            const close = tokens.matchBrace(tags, t, end) orelse break;
            t = close;
            continue;
        }
        // Skip fn declarations (proto + body).
        if (tags[t] == .keyword_fn) {
            t = tokens.skipFnDecl(tags, t, end);
            continue;
        }
        // Skip nested decls — `[pub] const/var Name ...;` — the
        // entire statement, terminator inclusive.  Without this we'd
        // misread `pub const empty: T = ...` as a field named `empty`.
        if (tags[t] == .keyword_pub or tags[t] == .keyword_const or
            tags[t] == .keyword_var or tags[t] == .keyword_comptime or
            tags[t] == .keyword_threadlocal)
        {
            const sc = tokens.findStmtSemicolon(tags, t, end) orelse break;
            t = sc;
            continue;
        }
        // Field shape: `<identifier>: <type-tokens>(= <default>)?,`
        if (tags[t] != .identifier) continue;
        if (t + 1 > end or tags[t + 1] != .colon) continue;
        // Walk the type expression until `=` (default) or `,` (terminator).
        const type_first: TokenIndex = t + 2;
        var type_last: TokenIndex = type_first;
        var d: u32 = 0;
        var has_default = false;
        var u: TokenIndex = type_first;
        while (u <= end) : (u += 1) {
            switch (tags[u]) {
                .l_paren, .l_brace, .l_bracket => d += 1,
                .r_paren, .r_brace, .r_bracket => if (d > 0) {
                    d -= 1;
                } else break,
                .equal => if (d == 0) {
                    has_default = true;
                    break;
                },
                .comma => if (d == 0) break,
                else => {},
            }
            type_last = u;
        }
        try out.append(a, .{
            .name = tree.tokenSlice(t),
            .name_token = t,
            .type_first = type_first,
            .type_last = type_last,
            .has_default = has_default,
        });
        // Advance past this field's terminator.
        if (u <= end and tags[u] == .equal) {
            // Skip default expression to the next `,` at depth 0.
            var dd: u32 = 0;
            while (u <= end) : (u += 1) {
                switch (tags[u]) {
                    .l_paren, .l_brace, .l_bracket => dd += 1,
                    .r_paren, .r_brace, .r_bracket => if (dd > 0) {
                        dd -= 1;
                    },
                    .comma => if (dd == 0) break,
                    else => {},
                }
            }
        }
        t = u;
    }
    return try out.toOwnedSlice(a);
}

fn collectMethods(
    a: std.mem.Allocator,
    tree: *const Ast,
    start: TokenIndex,
    end: TokenIndex,
    enclosing_type_name: []const u8,
) ![]const MethodInfo {
    var out: std.ArrayListUnmanaged(MethodInfo) = .empty;
    const tags = tree.tokens.items(.tag);
    if (start > end) return try out.toOwnedSlice(a);

    // Walk fn_decl nodes whose proto's name token is in [start, end]
    // AND not inside a nested brace within [start, end].
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buf, node) orelse continue;
        const name_tok = proto.name_token orelse continue;
        if (name_tok < start or name_tok > end) continue;
        // Reject if inside a nested type body (depth > 0 at name_tok).
        if (isInsideNestedBrace(tags, start, end, name_tok)) continue;
        const body = tokens.bodyOf(tree, node) orelse continue;

        try out.append(a, .{
            .name = tree.tokenSlice(name_tok),
            .name_token = name_tok,
            .fn_decl = node,
            .body = body,
            .body_first = tree.firstToken(body),
            .body_last = tree.lastToken(body),
            .is_pub = isPrecededByPub(tags, name_tok),
            .receiver = extractReceiver(tree, proto, enclosing_type_name),
        });
    }
    return try out.toOwnedSlice(a);
}

/// True if `tok` is inside a `{...}` block nested within `[start, end]`
/// (i.e., the depth at `tok` measured from `start` is > 0).
fn isInsideNestedBrace(
    tags: []const TokenTag,
    start: TokenIndex,
    end: TokenIndex,
    tok: TokenIndex,
) bool {
    var depth: u32 = 0;
    var t: TokenIndex = start;
    while (t <= end and t <= tok) : (t += 1) {
        if (t == tok) return depth > 0;
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => if (depth > 0) {
                depth -= 1;
            },
            else => {},
        }
    }
    return false;
}

/// `pub` directly before `fn name` — checked at `name_token - 2`
/// (the `fn` keyword is at `name_token - 1`).
fn isPrecededByPub(tags: []const TokenTag, name_token: TokenIndex) bool {
    if (name_token < 2) return false;
    if (tags[name_token - 1] != .keyword_fn) return false;
    return tags[name_token - 2] == .keyword_pub;
}

fn extractReceiver(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    enclosing_type_name: []const u8,
) ?Receiver {
    var it = proto.iterate(tree);
    const first = it.next() orelse return null;
    const name_tok = first.name_token orelse return null;
    const name = tree.tokenSlice(name_tok);
    const tags = tree.tokens.items(.tag);
    // Find the type tokens — they start after the parameter name's `:`.
    if (name_tok + 1 >= tree.tokens.len) return null;
    if (tags[name_tok + 1] != .colon) return null;
    var t = name_tok + 2;
    const type_first = t;
    var is_ptr = false;
    var is_const = false;
    if (t < tree.tokens.len and tags[t] == .asterisk) {
        is_ptr = true;
        t += 1;
        if (t < tree.tokens.len and tags[t] == .keyword_const) {
            is_const = true;
            t += 1;
        }
    }
    // The type should be `Self` or the enclosing type name, OR
    // the parameter should be named self/this.  Otherwise we can't
    // confidently call this a receiver — return null.
    const is_self_or_this = std.mem.eql(u8, name, "self") or std.mem.eql(u8, name, "this");
    if (t < tree.tokens.len and tags[t] == .identifier) {
        const tname = tree.tokenSlice(t);
        if (std.mem.eql(u8, tname, "Self") or std.mem.eql(u8, tname, enclosing_type_name)) {
            return .{
                .name = name,
                .name_token = name_tok,
                .is_ptr = is_ptr,
                .is_const = is_const,
            };
        }
    }
    if (is_self_or_this) {
        return .{
            .name = name,
            .name_token = name_tok,
            .is_ptr = is_ptr,
            .is_const = is_const,
        };
    }
    _ = type_first;
    return null;
}

fn protoReturnsErrorUnion(tree: *const Ast, proto: Ast.full.FnProto) bool {
    const rt = proto.ast.return_type.unwrap() orelse return false;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(rt);
    // `!T` — the `!` is the token IMMEDIATELY before the return-type
    // AST node's first token (the AST stores just `T` as the return type).
    // Also handles `E!T` (e.g. `error{Foo}!void`) where the bang is
    // somewhere inside the span; checking `first - 1` is enough for
    // the common `!T` form, and the explicit-error form has a `!`
    // inside the type's token range.
    if (first > 0 and tags[first - 1] == .bang) return true;
    const last_rt = tree.lastToken(rt);
    return tokens.hasTokenInRange(tags, first, last_rt, .bang);
}

// ── Tests ──────────────────────────────────────────────────

const testing = std.testing;

test "build: single struct with deinit + field" {
    const src: [:0]const u8 =
        \\const Outer = struct {
        \\    inner: Inner,
        \\    count: u32 = 0,
        \\    pub fn deinit(self: *Outer) void {
        \\        _ = self;
        \\    }
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expectEqual(@as(usize, 1), model.types.len);
    const ti = &model.types[0];
    try testing.expectEqualStrings("Outer", ti.name);
    try testing.expectEqual(TypeKind.struct_, ti.kind);
    try testing.expectEqual(@as(usize, 2), ti.fields.len);
    try testing.expectEqualStrings("inner", ti.fields[0].name);
    try testing.expectEqualStrings("count", ti.fields[1].name);
    try testing.expect(!ti.fields[0].has_default);
    try testing.expect(ti.fields[1].has_default);
    try testing.expect(ti.hasMethod("deinit"));
    try testing.expect(!ti.hasMethod("init"));
    try testing.expect(ti.hasCleanupMethod());
}

test "build: two structs in one file, type lookup" {
    const src: [:0]const u8 =
        \\const Inner = struct {
        \\    x: u32,
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\    pub fn deinit(self: *Outer) void { _ = self; }
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expectEqual(@as(usize, 2), model.types.len);
    try testing.expect(model.findType("Inner") != null);
    try testing.expect(model.findType("Outer") != null);
    try testing.expect(model.findType("Missing") == null);
    try testing.expect(model.typeHasMethod("Inner", "deinit"));
    try testing.expect(!model.typeHasMethod("Inner", "close"));
}

test "build: receiver detection" {
    const src: [:0]const u8 =
        \\const T = struct {
        \\    pub fn ptrSelf(self: *T) void { _ = self; }
        \\    pub fn constPtrSelf(self: *const T) void { _ = self; }
        \\    pub fn valueSelf(self: T) void { _ = self; }
        \\    pub fn aliasSelf(this: *T) void { _ = this; }
        \\    pub fn customRecv(t: *T) void { _ = t; }
        \\    pub fn noRecv() void {}
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    const ti = model.findType("T").?;
    const m_ptr = ti.findMethod("ptrSelf").?;
    try testing.expect(m_ptr.receiver != null);
    try testing.expect(m_ptr.receiver.?.is_ptr);
    try testing.expect(!m_ptr.receiver.?.is_const);

    const m_const = ti.findMethod("constPtrSelf").?;
    try testing.expect(m_const.receiver.?.is_ptr);
    try testing.expect(m_const.receiver.?.is_const);

    const m_val = ti.findMethod("valueSelf").?;
    try testing.expect(m_val.receiver != null);
    try testing.expect(!m_val.receiver.?.is_ptr);

    const m_this = ti.findMethod("aliasSelf").?;
    try testing.expect(m_this.receiver != null);
    try testing.expectEqualStrings("this", m_this.receiver.?.name);

    // `t: *T` — recognized because type matches enclosing name.
    const m_custom = ti.findMethod("customRecv").?;
    try testing.expect(m_custom.receiver != null);

    // `noRecv()` — no params, no receiver.
    const m_no = ti.findMethod("noRecv").?;
    try testing.expect(m_no.receiver == null);
}

test "build: top-level fn (not a method)" {
    const src: [:0]const u8 =
        \\const T = struct {
        \\    pub fn method(self: *T) void { _ = self; }
        \\};
        \\pub fn topLevelFn(x: u32) !void {
        \\    _ = x;
        \\}
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expectEqual(@as(usize, 1), model.fns.len);
    const f = &model.fns[0];
    try testing.expectEqualStrings("topLevelFn", f.name);
    try testing.expect(f.is_pub);
    try testing.expect(f.returns_error_union);

    // The struct's `method` should NOT appear in model.fns —
    // it lives in T.methods.
    try testing.expect(model.findFn("method") == null);
}

test "build: union and enum" {
    const src: [:0]const u8 =
        \\const Tag = enum { a, b, c };
        \\const U = union(Tag) {
        \\    a: u32,
        \\    b: void,
        \\    c: f64,
        \\    pub fn kill(self: *U) void { _ = self; }
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expectEqual(@as(usize, 2), model.types.len);
    const tag = model.findType("Tag").?;
    try testing.expectEqual(TypeKind.enum_, tag.kind);

    const u = model.findType("U").?;
    try testing.expectEqual(TypeKind.union_, u.kind);
    try testing.expect(u.hasMethod("kill"));
}

test "build: empty source" {
    var tree = try Ast.parse(testing.allocator, "", .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();
    try testing.expectEqual(@as(usize, 0), model.types.len);
    try testing.expectEqual(@as(usize, 0), model.fns.len);
}

test "nested declarations require their qualified lookup path" {
    const src: [:0]const u8 =
        \\const Outer = struct {
        \\    x: u32,
        \\    pub fn deinit(self: *Outer) void { _ = self; }
        \\    const Inner = struct {
        \\        y: u32,
        \\        pub fn close(self: *Inner) void { _ = self; }
        \\    };
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    const outer = model.findType("Outer").?;
    const inner = model.findType("Outer.Inner").?;
    try testing.expect(model.findType("Inner") == null);
    try testing.expect(model.findTypeInScope("Inner", outer) == inner);
    try testing.expect(outer.hasMethod("deinit"));
    try testing.expect(inner.hasMethod("close"));
    try testing.expect(inner.hasCleanupMethod());
}

test "fieldIsPointer: detects *T / ?*T / *const T" {
    const src: [:0]const u8 =
        \\const Foo = struct {
        \\    val: Inner,
        \\    ptr: *Inner,
        \\    opt_ptr: ?*Inner,
        \\    const_ptr: *const Inner,
        \\    opt_val: ?Inner,
        \\    sl: []u8,
        \\};
        \\const Inner = struct {};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expect(!model.fieldIsPointer("Foo", "val"));
    try testing.expect(model.fieldIsPointer("Foo", "ptr"));
    try testing.expect(model.fieldIsPointer("Foo", "opt_ptr"));
    try testing.expect(model.fieldIsPointer("Foo", "const_ptr"));
    try testing.expect(!model.fieldIsPointer("Foo", "opt_val"));
    try testing.expect(!model.fieldIsPointer("Foo", "sl"));
}

test "containingTypeOf: method's fn_decl resolves to its struct" {
    const src: [:0]const u8 =
        \\const Foo = struct {
        \\    x: u32,
        \\    pub fn deinit(self: *Foo) void { _ = self; }
        \\};
        \\pub fn top_level() void {}
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    // Find the deinit fn_decl + the top_level fn_decl.
    var idx: u32 = 1;
    var deinit_node: ?Ast.Node.Index = null;
    var top_node: ?Ast.Node.Index = null;
    while (idx < tree.nodes.len) : (idx += 1) {
        const n: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(n) != .fn_decl) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const fp = tokens.fnProto(&tree, &buf, n).?;
        const name_tok = fp.name_token.?;
        if (std.mem.eql(u8, tree.tokenSlice(name_tok), "deinit")) deinit_node = n;
        if (std.mem.eql(u8, tree.tokenSlice(name_tok), "top_level")) top_node = n;
    }
    const dt = model.containingTypeOf(deinit_node.?);
    try testing.expect(dt != null);
    try testing.expectEqualStrings("Foo", dt.?.name);
    try testing.expect(model.containingTypeOf(top_node.?) == null);
}

test "named field types distinguish wrappers from slices" {
    const src: [:0]const u8 =
        \\const Bar = struct {
        \\    a: Inner,
        \\    b: *Inner,
        \\    c: ?*const Inner,
        \\    d: []const u8,
        \\    e: ?Inner,
        \\};
        \\const Inner = struct {};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expectEqualStrings("Inner", model.fieldType("Bar", "a").?);
    try testing.expectEqualStrings("Inner", model.fieldType("Bar", "b").?);
    try testing.expectEqualStrings("Inner", model.fieldType("Bar", "c").?);
    try testing.expect(model.fieldType("Bar", "d") == null);
    try testing.expectEqualStrings("Inner", model.fieldType("Bar", "e").?);
}

test "isFlagOwnedField: detects X + X_allocated pair" {
    const src: [:0]const u8 =
        \\const Owner = struct {
        \\    data: []u8,
        \\    data_allocated: bool,
        \\    other: u32,
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    try testing.expect(model.isFlagOwnedField("Owner", "data"));
    try testing.expect(!model.isFlagOwnedField("Owner", "other"));
    try testing.expect(!model.isFlagOwnedField("Owner", "data_allocated"));
    try testing.expect(!model.isFlagOwnedField("Missing", "data"));
}

test "flagOwnedFields: returns the field-name set" {
    const src: [:0]const u8 =
        \\const Owner = struct {
        \\    one: []u8,
        \\    one_allocated: bool,
        \\    two: []u8,
        \\    two_allocated: bool,
        \\    three: u32,
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    const flagged = try model.flagOwnedFields(testing.allocator, "Owner");
    defer testing.allocator.free(flagged);
    try testing.expectEqual(@as(usize, 2), flagged.len);
    try testing.expectEqualStrings("one", flagged[0]);
    try testing.expectEqualStrings("two", flagged[1]);
}

test "qualified paths traverse multiple container scopes" {
    const src: [:0]const u8 =
        \\const A = struct {
        \\    const B = struct {
        \\        const C = struct { x: u32 };
        \\    };
        \\};
    ;
    var tree = try Ast.parse(testing.allocator, src, .zig);
    defer tree.deinit(testing.allocator);
    var model = try build(testing.allocator, &tree);
    defer model.deinit();

    const a = model.findType("A").?;
    const b = model.findType("A.B").?;
    const c = model.findType("A.B.C").?;
    try testing.expect(model.resolveTypeNameInScope("B.C", a) == c);
    try testing.expect(model.findTypeInScope("C", b) == c);
    try testing.expect(model.findType("B") == null);
    try testing.expect(model.findType("C") == null);
}
