// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// violations.zig — the subset's negative corpus (gate G10).
//
// Every construct here is banned by §2.4 of the specification. `atoma check`
// must reject the file and must name each violation with its own code. This
// file is never compiled: it exists to prove that the checker is not vacuous.
//
// If a future edit makes `atoma check` accept this file, the subset is no
// longer enforced and every claim in the specification that rests on "the
// subset is checked" becomes false. The gate fails in that case.

const std = @import("std");

// E-GLOBAL-VAR: ambient mutable state at container scope.
var global_counter: u32 = 0;

// E-ABI-PACKED: bit-level layout has no padding model.
pub const PackedBits = packed struct {
    a: u1,
    b: u7,
};

// E-ABI-WIDTH: `usize` is 32 bits on wasm32 and 64 elsewhere, so a C header
// generated for one target is wrong on the other (measured: F0.3).
pub const BadOut = extern struct {
    n: usize,
    flag: bool,
    opaque_ptr: ?*anyopaque,
};

// E-ABI-UNION: a bare union at the seam.
pub const BadUnion = extern union {
    a: u32,
    b: u64,
};

pub fn smuggledC(ptr: [*c]u8) void {
    // E-PTR-C: nullable, arithmetic-enabled, no length — three disciplines lost.
    _ = ptr;
}

pub fn castsAround(p: *u8) void {
    // E-PTR-CAST
    const q: *u8 = @ptrCast(p);
    // E-PTR-INT: never allowed, at any phase.
    const r: *u8 = @ptrFromInt(0x1000);
    _ = q;
    _ = r;
}

pub fn forbiddenPrimitives() void {
    // E-ASM
    asm volatile ("nop");
    // E-UNREACHABLE: UB in release modes.
    if (false) unreachable;
    // E-PANIC
    @panic("no");
}

pub fn ambientAuthority() void {
    // E-ALLOC-AMBIENT: an allocator the proof cannot name.
    const a = std.heap.c_allocator;
    _ = a;
}

pub fn includesEverything() void {
    // E-CIMPORT: an unbounded foreign surface.
    _ = @cImport(@cInclude("everything.h"));
}

pub fn unwraps(x: ?u32) u32 {
    // E-OPTIONAL-UNWRAP: panics on null.
    return x.?;
}

pub fn turnsOffChecks() void {
    // E-SAFETY-OFF: discharges every obligation by fiat.
    @setRuntimeSafety(false);
}

// E-UNCONTRACTED-EXPORT: an exported function with no `@contract` block.
export fn naked_export(x: u32) callconv(.c) u32 {
    return x;
}

// E-ABI-CALLCONV: the compiler rejects `.C` on every measured release.
export fn wrong_spelling(x: u32) callconv(.C) u32 {
    return x;
}
