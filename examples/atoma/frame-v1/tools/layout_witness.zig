// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// layout_witness.zig — Phase 0 "Layout & Signature Lock" witness generator.
//
// The ABI layout is *declared* in Idris2 (abi/FrameAbi.idr). This file does not
// compute layouts: it makes the Zig compiler *check* the declaration for the
// target it is compiled for and emit the checked rows in canonical `.cspec`
// form on stderr.
//
//   zig build-obj tools/layout_witness.zig -target <triple> -fno-emit-bin
//
// exits 0 iff every declared size / alignment / offset / padding range holds on
// <triple>. A drifted declaration is a compile error, so no target can silently
// produce a green run. `layout.sh` collects the rows.
//
// Nothing here is trusted: the Idris2 declaration is the specification, the
// compiler is the oracle, and the shell only transcribes what the compiler said.

const std = @import("std"); // comptimePrint only
const builtin = @import("builtin");

const witness = @import("layout_check.zig");

const FrameHeader = extern struct {
    magic: u16,
    length: u16,
    flags: u8,
    tag: u8,
    crc: u32,
    reserved: u16,
};

const FrameOut = extern struct {
    magic: u16,
    length: u16,
    flags: u8,
    tag: u8,
    crc: u32,
    payload: [*]const u8,
    payload_len: u32,
};

const arch = @tagName(builtin.cpu.arch);
const ptr_bits = @bitSizeOf(usize);

fn fieldRows(comptime T: type, comptime name: []const u8) void {
    inline for (@typeInfo(T).@"struct".fields) |f| {
        @compileLog(std.fmt.comptimePrint("field {s}@{s} {d} {d} {d} {s} {s}", .{
            name,
            arch,
            @offsetOf(T, f.name),
            @sizeOf(f.type),
            @alignOf(f.type),
            f.name,
            @typeName(f.type),
        }));
    }
}

comptime {
    witness.check(FrameHeader, "FrameHeader", .{
        .size = 16,
        .alignment = 4,
        .offsets = &.{ 0, 2, 4, 5, 8, 12 },
        .pads = &.{ 6, 8, 14, 16 },
    });
    fieldRows(FrameHeader, "FrameHeader");
    @compileLog("layout FrameHeader@" ++ arch ++ " 16 4 6..8,14..16");

    if (ptr_bits == 64) {
        witness.check(FrameOut, "FrameOut", .{
            .size = 32,
            .alignment = 8,
            .offsets = &.{ 0, 2, 4, 5, 8, 16, 24 },
            .pads = &.{ 6, 8, 12, 16, 28, 32 },
        });
        fieldRows(FrameOut, "FrameOut");
        @compileLog("layout FrameOut@" ++ arch ++ " 32 8 6..8,12..16,28..32");
    } else if (ptr_bits == 32) {
        witness.check(FrameOut, "FrameOut", .{
            .size = 20,
            .alignment = 4,
            .offsets = &.{ 0, 2, 4, 5, 8, 12, 16 },
            .pads = &.{ 6, 8 },
        });
        fieldRows(FrameOut, "FrameOut");
        @compileLog("layout FrameOut@" ++ arch ++ " 20 4 6..8");
    } else {
        @compileError("FrameOut layout is proven only for 32- and 64-bit pointers");
    }
}
