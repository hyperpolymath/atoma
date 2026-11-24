// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Serialize original source bytes and a complete authoritative byte table.
//! ScalarSource.v independently parses and interprets those bytes in Coq.
//! No Zig-side evaluator, lowering decision or success verdict enters a proof.
const std = @import("std");

pub fn contractTable(bytes: []const u8) ![256]u64 {
    var values: [256]u64 = undefined;
    var lines = std.mem.splitScalar(u8, bytes, '\n');
    var count: usize = 0;
    while (lines.next()) |line| {
        // Only the final empty line is permitted.
        if (line.len == 0 and count == 256 and lines.peek() == null) break;
        if (count == 256) return error.InvalidContractTable;
        var words = std.mem.tokenizeAny(u8, line, " \t\r");
        const index = words.next() orelse return error.InvalidContractTable;
        const value = words.next() orelse return error.InvalidContractTable;
        if (words.next() != null) return error.InvalidContractTable;
        if ((std.fmt.parseInt(usize, index, 10) catch return error.InvalidContractTable) != count)
            return error.InvalidContractTable;
        values[count] = std.fmt.parseInt(u64, value, 10) catch return error.InvalidContractTable;
        count += 1;
    }
    if (count != 256) return error.InvalidContractTable;
    return values;
}

fn sourceLiteral(w: *std.Io.Writer, bytes: []const u8) !void {
    try w.writeByte('[');
    for (bytes, 0..) |b, i| {
        if (i != 0) try w.writeAll("; ");
        try w.print("{d}", .{b});
    }
    try w.writeByte(']');
}
fn tableLiteral(w: *std.Io.Writer, values: [256]u64) !void {
    try w.writeByte('[');
    for (values, 0..) |value, i| {
        if (i != 0) try w.writeAll("; ");
        try w.print("{d}%N", .{value});
    }
    try w.writeByte(']');
}

pub fn emit(w: *std.Io.Writer, bytes: []const u8, table: []const u8, audit: bool) !void {
    if (bytes.len == 0 or bytes.len > 16384) return error.UnsupportedSourceSize;
    const values = try contractTable(table);
    try w.writeAll("From Coq Require Import List Arith NArith.\nRequire Import ScalarSource.\nImport ListNotations.\n");
    try w.writeAll("Definition source_bytes : list nat := ");
    try sourceLiteral(w, bytes);
    try w.writeAll(".\nDefinition specification : list N := ");
    try tableLiteral(w, values);
    try w.writeAll(".\n");
    if (audit) {
        try w.writeAll(
            \\Require AtomaProof.
            \\Check (AtomaProof.atoma_scalar : forall x, x < 256 ->
            \\  ScalarSource.run source_bytes x = Some (nth x specification 0%N)).
            \\Check (AtomaProof.atoma_scalar_range : forall x, x < 256 ->
            \\  exists result, ScalarSource.run source_bytes x = Some result /\ (result < N.pow 2 64)%N).
            \\Print Assumptions AtomaProof.atoma_scalar.
            \\Print Assumptions AtomaProof.atoma_scalar_range.
            \\
        );
    } else {
        try w.writeAll(
            \\Lemma source_accepted : ScalarSource.accepts source_bytes = true.
            \\Proof. vm_compute. reflexivity. Qed.
            \\Lemma table_checked : ScalarSource.check source_bytes specification = true.
            \\Proof. vm_compute. reflexivity. Qed.
            \\Theorem atoma_scalar : forall x, x < 256 ->
            \\  ScalarSource.run source_bytes x = Some (nth x specification 0%N).
            \\Proof. exact (ScalarSource.check_sound source_bytes specification table_checked). Qed.
            \\Theorem atoma_scalar_range : forall x, x < 256 ->
            \\  exists result, ScalarSource.run source_bytes x = Some result /\ (result < N.pow 2 64)%N.
            \\Proof. exact (ScalarSource.check_range source_bytes specification table_checked). Qed.
            \\Print Assumptions atoma_scalar.
            \\Print Assumptions atoma_scalar_range.
            \\
        );
    }
}

test "contract tables reject missing, reordered, oversized and extra rows" {
    try std.testing.expectError(error.InvalidContractTable, contractTable(""));
    try std.testing.expectError(error.InvalidContractTable, contractTable("1 0\n"));
    try std.testing.expectError(error.InvalidContractTable, contractTable("0 18446744073709551616\n"));
    var bytes = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer bytes.deinit();
    for (0..256) |i| try bytes.writer.print("{d} {d}\n", .{ i, i });
    const values = try contractTable(bytes.written());
    try std.testing.expectEqual(@as(u64, 255), values[255]);
    try bytes.writer.writeAll("256 0\n");
    try std.testing.expectError(error.InvalidContractTable, contractTable(bytes.written()));
}
