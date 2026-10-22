// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// layout_negative.zig — falsifier F0.3 for Phase 0.
//
// `BadOut` uses `usize` across the FFI seam. Its layout is pointer-width
// dependent (24 bytes / align 8 on 64-bit, 12 bytes / align 4 on wasm32), so a
// single declared layout cannot hold on both. This file declares the 64-bit
// layout; the Phase 0 gate asserts that
//
//     zig build-obj tools/layout_negative.zig -target wasm32-freestanding
//
// FAILS. If it ever succeeds, the layout witness is not witnessing anything and
// the whole Phase 0 gate is void.

const witness = @import("layout_check.zig");

const BadOut = extern struct {
    a: u8,
    n: usize, // ← banned across the seam: pointer-width dependent
    b: u32,
};

comptime {
    // The 64-bit layout, declared once. Correct on x86_64/aarch64/riscv64,
    // wrong on wasm32 — which is exactly the point.
    witness.check(BadOut, "BadOut", .{
        .size = 24,
        .alignment = 8,
        .offsets = &.{ 0, 8, 16 },
        .pads = &.{ 1, 8, 20, 24 },
    });
}
