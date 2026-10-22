// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// atoma.zig — the Atoma *trusted runtime primitives*.
//
// Everything the verified subset is allowed to do that plain Zig expresses with
// a banned construct lives here, once, with a stated model-level contract:
//
//   atoma.zeroBytes(p)   — every byte of `*p`, including padding, becomes 0x00.
//                       This is the ONLY sanctioned way to define padding.
//                       Zig's value assignment (`p.* = .{...}`) does NOT define
//                       padding bytes, so it can never discharge a padding VC.
//   atoma.isZeroed(p)    — the corresponding observation, used by tests and by
//                       runtime assertions on the FFI shell.
//
// `@memset` over `std.mem.asBytes` is the only pointer-cast-like operation in
// the trusted surface. `@ptrCast`, `@ptrFromInt` and `@alignCast` are banned in
// user code (spec §2.4); this file is the whitelisted kernel that replaces them.
// Its soundness argument is one line long and is stated in the spec: `asBytes`
// yields exactly @sizeOf(T) writable bytes of the live object, `@memset` writes
// each of them once, so the post-state has no undefined byte in `p`.

const std = @import("std");

/// Zero every byte of `*p`, padding included.
pub fn zeroBytes(p: anytype) void {
    @memset(std.mem.asBytes(p), 0);
}

/// True iff `p` was zeroed with `zeroBytes` (or is otherwise all-zero).
pub fn isZeroed(p: anytype) bool {
    for (std.mem.asBytes(p)) |b| {
        if (b != 0) return false;
    }
    return true;
}

/// True iff every byte of `*p` that is *not* a field byte is zero.
/// Field coverage is computed from the type, so this is target-aware: it follows
/// @sizeOf/@offsetOf for whatever target the test binary was built for.
pub fn paddingIsZero(p: anytype) bool {
    const T = @TypeOf(p.*);
    const N = @sizeOf(T);
    var covered = [_]bool{false} ** N;
    inline for (comptime fieldNames(T)) |name| {
        const off = @offsetOf(T, name);
        const sz = @sizeOf(@FieldType(T, name));
        var i: usize = off;
        while (i < off + sz) : (i += 1) covered[i] = true;
    }
    const bytes = std.mem.asBytes(p);
    var i: usize = 0;
    while (i < N) : (i += 1) {
        if (!covered[i] and bytes[i] != 0) return false;
    }
    return true;
}

fn fieldNames(comptime T: type) []const []const u8 {
    comptime {
        const fields = @typeInfo(T).@"struct".fields;
        var names: [fields.len][]const u8 = undefined;
        for (fields, 0..) |f, i| names[i] = f.name;
        const final = names;
        return &final;
    }
}
