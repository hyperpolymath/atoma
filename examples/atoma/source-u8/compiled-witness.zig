// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
const std = @import("std");
extern fn increment(x: u8) callconv(.c) u8;

test "compiled pilot matches the contract for every u8 input" {
    for (0..256) |i| {
        const x: u8 = @intCast(i);
        try std.testing.expectEqual(x +% @as(u8, 1), increment(x));
    }
}
