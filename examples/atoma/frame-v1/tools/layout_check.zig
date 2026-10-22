// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// layout_check.zig — the comptime layout oracle. No std, no runtime: it is
// evaluated during semantic analysis and either compiles or does not.
//
// The declaration it checks comes from Idris2 (abi/FrameAbi.idr); the values it
// compares against come from the Zig compiler itself (@sizeOf/@alignOf/@offsetOf).
// A disagreement is a compile error, so a drifted layout cannot be witnessed.

pub const Expect = struct {
    size: usize,
    alignment: usize,
    /// Field offsets, in declaration order.
    offsets: []const usize,
    /// Padding byte ranges, as (start, end) pairs.
    pads: []const usize,
};

pub fn check(comptime T: type, comptime name: []const u8, comptime e: Expect) void {
    if (@sizeOf(T) != e.size) @compileError(name ++ ": declared size != @sizeOf");
    if (@alignOf(T) != e.alignment) @compileError(name ++ ": declared alignment != @alignOf");
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len != e.offsets.len) @compileError(name ++ ": declared field count != actual");
    inline for (fields, 0..) |f, i| {
        if (@offsetOf(T, f.name) != e.offsets[i]) @compileError(name ++ ": declared offset != @offsetOf");
    }
    // Padding is re-derived as the complement of the field byte ranges; the
    // declared ranges must agree with it byte for byte.
    var covered = [_]bool{false} ** 128;
    inline for (fields) |f| {
        const off = @offsetOf(T, f.name);
        const sz = @sizeOf(f.type);
        for (off..off + sz) |i| covered[i] = true;
    }
    var i: usize = 0;
    while (i < @sizeOf(T)) : (i += 1) {
        const is_pad = !covered[i];
        var declared = false;
        var k: usize = 0;
        while (k < e.pads.len) : (k += 2) {
            if (i >= e.pads[k] and i < e.pads[k + 1]) declared = true;
        }
        if (is_pad != declared) @compileError(name ++ ": declared padding != field complement");
    }
}

