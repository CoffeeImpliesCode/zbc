//! Receiver / method-name classifiers.
//!
//! Per-rule precision iteration revealed that the same set of
//! name-based filters keeps coming up:
//!   - "is this an allocator receiver name?"
//!   - "is this self / this?"
//!   - "is this a canonical out-param name?"
//!   - "is this a cleanup method (deinit / free / etc.)?"
//!   - "is this an addref / release method?"
//!
//! Before this module, each rule reimplemented these with slight
//! variations (one rule had `allocator`-suffix matching, another
//! didn't; one accepted `gpa`, another didn't).  Centralizing
//! keeps the rules consistent and fixes get rolled out everywhere.

const std = @import("std");

// ── Receiver names ────────────────────────────────────────

/// Conservative allowlist of identifiers that look like an
/// allocator handle.  Matches by suffix / substring patterns
/// rather than an exact list to handle project-specific
/// allocator names (`string_alloc`, `grapheme_alloc`,
/// `default_allocator`, etc.).
pub fn isAllocatorishName(name: []const u8) bool {
    if (name.len == 0) return false;
    if (std.mem.eql(u8, name, "gpa")) return true;
    if (std.mem.eql(u8, name, "alloc")) return true;
    if (std.mem.eql(u8, name, "allocator")) return true;
    if (std.mem.eql(u8, name, "a")) return true;
    if (std.mem.endsWith(u8, name, "_alloc")) return true;
    if (std.mem.endsWith(u8, name, "_allocator")) return true;
    if (std.mem.endsWith(u8, name, "_gpa")) return true;
    if (std.mem.endsWith(u8, name, "Alloc")) return true;
    if (std.mem.endsWith(u8, name, "Allocator")) return true;
    return false;
}

/// True for `self` / `this` — the canonical method-receiver
/// parameter names in Zig.
pub fn isSelfReceiverName(name: []const u8) bool {
    return std.mem.eql(u8, name, "self") or std.mem.eql(u8, name, "this");
}

/// True for `result` / `out` / `r` — canonical out-param names
/// used for in-place struct construction.
pub fn isCanonicalOutName(name: []const u8) bool {
    return std.mem.eql(u8, name, "result") or
        std.mem.eql(u8, name, "out") or
        std.mem.eql(u8, name, "r");
}

// ── Method classification ────────────────────────────────

/// Methods that destroy / clean up a resource.
pub fn isCleanupMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "close") or
        std.mem.eql(u8, name, "stop") or
        std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "deref") or
        std.mem.eql(u8, name, "unref") or
        std.mem.eql(u8, name, "removeRef") or
        std.mem.eql(u8, name, "finalize") or
        std.mem.eql(u8, name, "dispose");
}

/// Methods that acquire a refcounted reference (addref family).
/// `ref` alone is excluded — too generic, collides with
/// "borrow a sub-reference" usage.
pub fn isAcquireMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "reference") or
        std.mem.eql(u8, name, "retain") or
        std.mem.eql(u8, name, "addRef") or
        std.mem.eql(u8, name, "addref") or
        std.mem.eql(u8, name, "acquire") or
        std.mem.eql(u8, name, "pendingActivityRef");
}

/// Methods that release a refcounted reference (broader than
/// cleanup — used for the suppressor in `unreleased-refs-on-error`).
pub fn isReleaseMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "deref") or
        std.mem.eql(u8, name, "unref") or
        std.mem.eql(u8, name, "removeRef") or
        std.mem.eql(u8, name, "pendingActivityUnref");
}

/// Methods that conventionally allocate.
pub fn isAllocMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "allocSentinel") or
        std.mem.eql(u8, name, "allocAdvanced") or
        std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "dupeZ") or
        std.mem.eql(u8, name, "create") or
        std.mem.eql(u8, name, "allocPrint") or
        std.mem.eql(u8, name, "allocPrintZ") or
        std.mem.eql(u8, name, "allocPrintSentinel") or
        std.mem.eql(u8, name, "realloc");
}

/// ArrayList (and SegmentedList / similar) methods that may grow the
/// backing buffer — i.e. may reallocate and move the buffer pointer.
/// Any slice or element pointer into the buffer taken BEFORE one of
/// these calls may be invalidated AFTER the call.
///
/// Excludes `*AssumeCapacity` variants — those require the buffer to
/// already have sufficient capacity and cannot reallocate.
pub fn isArrayListGrowMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "appendNTimes") or
        std.mem.eql(u8, name, "insertAt") or
        std.mem.eql(u8, name, "insertSlice") or
        std.mem.eql(u8, name, "ensureCapacity") or
        std.mem.eql(u8, name, "ensureTotalCapacity") or
        std.mem.eql(u8, name, "ensureUnusedCapacity") or
        std.mem.eql(u8, name, "ensureTotalCapacityPrecise") or
        std.mem.eql(u8, name, "resize") or
        std.mem.eql(u8, name, "addOne") or
        std.mem.eql(u8, name, "addManyAsSlice") or
        std.mem.eql(u8, name, "addManyAsArray");
}

/// Container-mutation methods that STORE the caller's data into the
/// container's backing storage.  When the data is borrowed (e.g.
/// from an arena that's about to die), storing it through one of
/// these into a longer-lived container leaves a dangling slice.
pub fn isContainerStoreMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "appendNTimes") or
        std.mem.eql(u8, name, "insert") or
        std.mem.eql(u8, name, "insertSlice") or
        std.mem.eql(u8, name, "put") or
        std.mem.eql(u8, name, "putAssumeCapacity") or
        std.mem.eql(u8, name, "putNoClobber") or
        std.mem.eql(u8, name, "addOne") or
        std.mem.eql(u8, name, "addManyAsSlice");
}

/// Methods in JSC (JavaScriptCore) that dispatch into user JavaScript
/// code or otherwise trigger GC.  A raw byte slice taken from a
/// JSC-managed ArrayBuffer or JSString that is live across one of
/// these calls may be dangling — the GC may have moved or freed the
/// backing buffer.
pub fn isGcTriggerMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "call") or
        std.mem.eql(u8, name, "callAsFunction") or
        std.mem.eql(u8, name, "callAsConstructor") or
        std.mem.eql(u8, name, "callFunction") or
        std.mem.eql(u8, name, "evaluate") or
        std.mem.eql(u8, name, "evaluateExpression") or
        std.mem.eql(u8, name, "runMicrotasks") or
        std.mem.eql(u8, name, "dispatch") or
        std.mem.eql(u8, name, "invoke") or
        std.mem.eql(u8, name, "handleEvent") or
        std.mem.eql(u8, name, "collectGarbage") or
        std.mem.eql(u8, name, "runGC") or
        std.mem.eql(u8, name, "triggerGC");
}

/// Names used to acquire an additional reference on a refcounted
/// object.  A shallow copy of a struct containing a field of a
/// refcounted type — without first calling one of these — creates an
/// unbalanced decrement on drop.
pub fn isRefAcquireName(name: []const u8) bool {
    return std.mem.eql(u8, name, "ref") or
        std.mem.eql(u8, name, "retain") or
        std.mem.eql(u8, name, "addRef") or
        std.mem.eql(u8, name, "dupeRef") or
        std.mem.eql(u8, name, "clone") or
        std.mem.eql(u8, name, "copy") or
        std.mem.eql(u8, name, "strongRef") or
        std.mem.eql(u8, name, "reference") or
        std.mem.eql(u8, name, "acquireRef") or
        std.mem.eql(u8, name, "incRef");
}

/// Bare function names used to register a callback that may run on
/// any thread (at-exit handlers, signal handlers, cross-thread task
/// queues).  A function registered via one of these may be called
/// concurrently with main-thread data structures.
pub fn isExitCallbackRegisterName(name: []const u8) bool {
    return std.mem.eql(u8, name, "add_exit_callback") or
        std.mem.eql(u8, name, "addExitCallback") or
        std.mem.eql(u8, name, "onExit") or
        std.mem.eql(u8, name, "atexit") or
        std.mem.eql(u8, name, "addAtExit") or
        std.mem.eql(u8, name, "registerAtExit") or
        std.mem.eql(u8, name, "onSignal") or
        std.mem.eql(u8, name, "addSignalHandler");
}

/// Method names that push a new scope/frame/context onto a stack.
/// Must be balanced with a corresponding pop/exit call on all exit
/// paths — ideally via `defer`.
pub fn isScopePushMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "pushScope") or
        std.mem.eql(u8, name, "push_scope") or
        std.mem.eql(u8, name, "enterScope") or
        std.mem.eql(u8, name, "enter_scope") or
        std.mem.eql(u8, name, "pushContext") or
        std.mem.eql(u8, name, "enterContext") or
        std.mem.eql(u8, name, "pushFrame") or
        std.mem.eql(u8, name, "beginScope") or
        std.mem.eql(u8, name, "openScope") or
        std.mem.eql(u8, name, "pushNamespace") or
        std.mem.eql(u8, name, "enterNamespace");
}

/// Counterparts to isScopePushMethodName.  Must appear on every exit
/// path of a function that called a push method — or under a `defer`
/// that fires unconditionally.
pub fn isScopePopMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "popScope") or
        std.mem.eql(u8, name, "pop_scope") or
        std.mem.eql(u8, name, "exitScope") or
        std.mem.eql(u8, name, "exit_scope") or
        std.mem.eql(u8, name, "popContext") or
        std.mem.eql(u8, name, "exitContext") or
        std.mem.eql(u8, name, "popFrame") or
        std.mem.eql(u8, name, "endScope") or
        std.mem.eql(u8, name, "closeScope") or
        std.mem.eql(u8, name, "popNamespace") or
        std.mem.eql(u8, name, "exitNamespace");
}

// ── Tests ──────────────────────────────────────────────────

test "isAllocatorishName" {
    const t = std.testing;
    try t.expect(isAllocatorishName("gpa"));
    try t.expect(isAllocatorishName("allocator"));
    try t.expect(isAllocatorishName("string_alloc"));
    try t.expect(isAllocatorishName("graphemeAllocator"));
    try t.expect(isAllocatorishName("test_gpa"));
    try t.expect(isAllocatorishName("arena_gpa"));
    try t.expect(!isAllocatorishName("self"));
    try t.expect(!isAllocatorishName("buffer"));
}

test "isSelfReceiverName" {
    const t = std.testing;
    try t.expect(isSelfReceiverName("self"));
    try t.expect(isSelfReceiverName("this"));
    try t.expect(!isSelfReceiverName("it"));
    try t.expect(!isSelfReceiverName("inspector"));
}

test "isAllocMethodName" {
    const t = std.testing;
    try t.expect(isAllocMethodName("alloc"));
    try t.expect(isAllocMethodName("create"));
    try t.expect(isAllocMethodName("dupe"));
    try t.expect(isAllocMethodName("realloc"));
    try t.expect(isAllocMethodName("allocPrint"));
    try t.expect(isAllocMethodName("allocAdvanced"));
    try t.expect(!isAllocMethodName("free"));
    try t.expect(!isAllocMethodName("destroy"));
    try t.expect(!isAllocMethodName("deinit"));
    try t.expect(!isAllocMethodName("totally_made_up_method"));
}

test "method classifiers don't overlap incorrectly" {
    const t = std.testing;
    try t.expect(isCleanupMethodName("deinit"));
    try t.expect(isCleanupMethodName("stop"));
    try t.expect(isAcquireMethodName("reference"));
    try t.expect(!isAcquireMethodName("ref")); // too generic
    try t.expect(isReleaseMethodName("release"));
    try t.expect(isReleaseMethodName("pendingActivityUnref"));
}

test "isGcTriggerMethodName" {
    const t = std.testing;
    try t.expect(isGcTriggerMethodName("call"));
    try t.expect(isGcTriggerMethodName("callAsFunction"));
    try t.expect(isGcTriggerMethodName("callAsConstructor"));
    try t.expect(isGcTriggerMethodName("callFunction"));
    try t.expect(isGcTriggerMethodName("evaluate"));
    try t.expect(isGcTriggerMethodName("evaluateExpression"));
    try t.expect(isGcTriggerMethodName("runMicrotasks"));
    try t.expect(isGcTriggerMethodName("dispatch"));
    try t.expect(isGcTriggerMethodName("invoke"));
    try t.expect(isGcTriggerMethodName("handleEvent"));
    try t.expect(isGcTriggerMethodName("collectGarbage"));
    try t.expect(isGcTriggerMethodName("runGC"));
    try t.expect(isGcTriggerMethodName("triggerGC"));
    try t.expect(!isGcTriggerMethodName("append"));
    try t.expect(!isGcTriggerMethodName("deinit"));
    try t.expect(!isGcTriggerMethodName("totally_made_up"));
}

test "isRefAcquireName" {
    const t = std.testing;
    try t.expect(isRefAcquireName("ref"));
    try t.expect(isRefAcquireName("retain"));
    try t.expect(isRefAcquireName("addRef"));
    try t.expect(isRefAcquireName("dupeRef"));
    try t.expect(isRefAcquireName("clone"));
    try t.expect(isRefAcquireName("copy"));
    try t.expect(isRefAcquireName("strongRef"));
    try t.expect(isRefAcquireName("reference"));
    try t.expect(isRefAcquireName("acquireRef"));
    try t.expect(isRefAcquireName("incRef"));
    try t.expect(!isRefAcquireName("release"));
    try t.expect(!isRefAcquireName("unref"));
    try t.expect(!isRefAcquireName("totally_made_up"));
}

test "isExitCallbackRegisterName" {
    const t = std.testing;
    try t.expect(isExitCallbackRegisterName("add_exit_callback"));
    try t.expect(isExitCallbackRegisterName("addExitCallback"));
    try t.expect(isExitCallbackRegisterName("onExit"));
    try t.expect(isExitCallbackRegisterName("atexit"));
    try t.expect(isExitCallbackRegisterName("addAtExit"));
    try t.expect(isExitCallbackRegisterName("registerAtExit"));
    try t.expect(isExitCallbackRegisterName("onSignal"));
    try t.expect(isExitCallbackRegisterName("addSignalHandler"));
    try t.expect(!isExitCallbackRegisterName("append"));
    try t.expect(!isExitCallbackRegisterName("deinit"));
    try t.expect(!isExitCallbackRegisterName("totally_made_up"));
}

test "isScopePushMethodName" {
    const t = std.testing;
    try t.expect(isScopePushMethodName("pushScope"));
    try t.expect(isScopePushMethodName("push_scope"));
    try t.expect(isScopePushMethodName("enterScope"));
    try t.expect(isScopePushMethodName("enter_scope"));
    try t.expect(isScopePushMethodName("pushContext"));
    try t.expect(isScopePushMethodName("enterContext"));
    try t.expect(isScopePushMethodName("pushFrame"));
    try t.expect(isScopePushMethodName("beginScope"));
    try t.expect(isScopePushMethodName("openScope"));
    try t.expect(isScopePushMethodName("pushNamespace"));
    try t.expect(isScopePushMethodName("enterNamespace"));
    try t.expect(!isScopePushMethodName("popScope"));
    try t.expect(!isScopePushMethodName("exitScope"));
    try t.expect(!isScopePushMethodName("totally_made_up"));
}

test "isScopePopMethodName" {
    const t = std.testing;
    try t.expect(isScopePopMethodName("popScope"));
    try t.expect(isScopePopMethodName("pop_scope"));
    try t.expect(isScopePopMethodName("exitScope"));
    try t.expect(isScopePopMethodName("exit_scope"));
    try t.expect(isScopePopMethodName("popContext"));
    try t.expect(isScopePopMethodName("exitContext"));
    try t.expect(isScopePopMethodName("popFrame"));
    try t.expect(isScopePopMethodName("endScope"));
    try t.expect(isScopePopMethodName("closeScope"));
    try t.expect(isScopePopMethodName("popNamespace"));
    try t.expect(isScopePopMethodName("exitNamespace"));
    try t.expect(!isScopePopMethodName("pushScope"));
    try t.expect(!isScopePopMethodName("enterScope"));
    try t.expect(!isScopePopMethodName("totally_made_up"));
}
