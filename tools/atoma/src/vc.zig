// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Atoma — the VC generator for the frame-v1 worked example.
//
// This file is *untrusted plumbing*: it emits SMT-LIB queries, and what it
// proves is whatever the solver says about them. It replaces `vc/gen_vcs.py`,
// which the estate's language policy forbids — `governance / Language /
// package anti-pattern policy` runs `git ls-files '*.py'` and fails the PR.
// The port is deliberate rather than cosmetic: the generator is deterministic,
// dependency-free and diffable against the checked-in artefacts, and the
// solver is invoked directly by `verify.sh` instead of through a Python API.
//
// Two families of query are produced for each obligation:
//
//   positive  premises /\ not goal      must be UNSAT  (obligation discharged)
//   needle    the load-bearing premise removed          must be SAT
//
// The `needle` family is what stops a contract from being vacuously true: if a
// precondition can be deleted without turning the goal into a counterexample,
// that precondition was doing no work, and the mutation harness must say so.
//
// Output is ASCII, LF-terminated and byte-stable: same input, same bytes, on
// every machine. `verify.sh` regenerates into a temporary directory and diffs,
// so a hand-edited `.smt2` cannot survive.
//
// Spec: docs/spec/ATOMA-SPEC.adoc §7 (obligations) and §8.3 (the VC set).

const std = @import("std");
const Allocator = std.mem.Allocator;

pub const Expected = enum {
    unsat,
    sat,

    pub fn name(self: Expected) []const u8 {
        return switch (self) {
            .unsat => "unsat",
            .sat => "sat",
        };
    }
};

pub const Vc = struct {
    name: []const u8,
    kind: []const u8,
    why: []const u8,
    expected: Expected,
};

/// Canonical lines that the fourteen queries are *derived from*. `atoma vc`
/// refuses to emit anything unless the contract it is pointed at still contains
/// every one of them: if the contract moved, the queries describe a program that
/// no longer exists, and emitting them anyway is exactly the kind of silent
/// staleness this project exists to prevent. Values are in canonical (decimal)
/// form because that is what `atoma canon` prints.
pub const contract_facts = [_][]const u8{
    "requires ( <= 12 ( len input ) )",
    "requires ( < input_len 4294967296 )",
    "ensures ( => ( = res 0 ) ( = ( magic out ) 21569 ) )",
    "ensures ( => ( = res 0 ) ( <= ( payload_len out ) ( - ( len input ) 12 ) ) )",
    "bound steps ( + 12 ( * 8 input_len ) )",
};

pub const ContractDrift = error{ContractDrift};

/// Fail-closed binding to the contract: every fact the queries encode must
/// still be present, verbatim, in the canonical contract.
pub fn checkContract(canonical: []const u8) ContractDrift!void {
    for (contract_facts) |f| {
        if (std.mem.indexOf(u8, canonical, f) == null) return error.ContractDrift;
    }
}

/// The VC set, in the order the receipt hashes it. Fixed order matters: the
/// aggregate content address is taken over the per-file hashes in this order,
/// so reordering is a different VC set even if the members are equal.
pub const vcs = [_]Vc{
    .{ .name = "V1_no_underflow", .kind = "arith", .expected = .unsat,
       .why = "`buf.len - 12` cannot wrap once len >= 12 is known" },
    .{ .name = "V1_needle_drop_requires", .kind = "arith", .expected = .sat,
       .why = "without `len >= 12` the subtraction underflows: model is the panic" },
    .{ .name = "V2_slice_in_bounds", .kind = "bounds", .expected = .unsat,
       .why = "12 + length <= buf.len, so buf[12 .. 12+length] is in bounds" },
    .{ .name = "V2_needle_drop_payload_bound", .kind = "bounds", .expected = .sat,
       .why = "a frame claiming more bytes than the buffer holds slices out of bounds" },
    .{ .name = "V2_mutant_off_by_one", .kind = "bounds", .expected = .sat,
       .why = "`avail + 1` admits exactly one byte past the end: off-by-one" },
    .{ .name = "V3_intcast_range", .kind = "cast", .expected = .unsat,
       .why = "a slice from a u32 in_len is at most 2^32-1 bytes and at least 12, so the usize-to-u32 @intCast cannot trap" },
    .{ .name = "V3_needle_drop_ffi_bound", .kind = "cast", .expected = .sat,
       .why = "called directly with a >4GiB slice, the same @intCast panics" },
    .{ .name = "V4_maxplus_bound", .kind = "cost", .expected = .unsat,
       .why = "8 steps per payload byte; worst case 8*65535+12 < 2^32 so the MaxPlus bound is representable in the cost domain" },
    .{ .name = "V5_magic_wire_order", .kind = "abi", .expected = .unsat,
       .why = "bytes 'A','T' decode to 0x5441; the 'obvious' 0x4154 would put 'T','A' on the wire" },
    .{ .name = "V5_mutant_wrong_endian", .kind = "abi", .expected = .unsat,
       .why = "0x4154 is refuted by the same bytes: the literal ASCII word is wrong" },
    .{ .name = "V6_padding_zeroed", .kind = "layout", .expected = .unsat,
       .why = "writes hit only field bytes, so every padding byte keeps the 0x00 it got from zeroBytes" },
    .{ .name = "V6_mutant_offset_drift", .kind = "layout", .expected = .sat,
       .why = "a payload placed at offset 12 writes into the padding hole 12..16: the padding VC catches layout drift" },
    .{ .name = "V7_post_payload_len", .kind = "post", .expected = .unsat,
       .why = "the success postcondition follows from the guard that produced success" },
    .{ .name = "V8_premise_satisfiable", .kind = "vacuity", .expected = .sat,
       .why = "a contradictory precondition would make every VC trivially UNSAT, so satisfiability of the premises is a VC in its own right" },
};

/// The `FrameOut` field bytes on a 64-bit target: (offset, size) pairs, read
/// from `spec/layout.cspec`. A drift here is what V6_mutant_offset_drift
/// detects, so this table and the layout witness must agree.
const frame_out_fields = [_]struct { off: u32, size: u32 }{
    .{ .off = 0, .size = 2 }, // magic
    .{ .off = 2, .size = 2 }, // payload_len
    .{ .off = 4, .size = 1 }, // flags
    .{ .off = 5, .size = 1 }, // tag
    .{ .off = 8, .size = 4 }, // crc32
    .{ .off = 16, .size = 8 }, // payload pointer: the field that drifts
    .{ .off = 24, .size = 4 }, // payload_len_u32
};

/// Offset of the payload pointer in the witnessed layout. The drift query moves
/// exactly this field, which is the mistake an author makes when one target's
/// `@offsetOf` is transcribed wrongly.
const payload_offset_witnessed: u32 = 16;
const payload_offset_drifted: u32 = 12;

const pad_bytes_64 = [_]u32{ 6, 7, 12, 13, 14, 15, 28, 29, 30, 31 };

fn line(w: anytype, comptime fmt: []const u8, args: anytype) !void {
    try w.print(fmt ++ "\n", args);
}

fn header(w: anytype, v: Vc) !void {
    try line(w, "; SPDX-License-Identifier: MPL-2.0", .{});
    try line(w, "; generated by `atoma vc` - {s} ({s})", .{ v.name, v.kind });
    try line(w, "; {s}", .{v.why});
    try line(w, "; expected: {s}", .{switch (v.expected) {
        .unsat => "UNSAT",
        .sat => "SAT",
    }});
}

fn decl(w: anytype, name: []const u8, width: u8) !void {
    try line(w, "(declare-const {s} (_ BitVec {d}))", .{ name, width });
}

/// `(store (store … base i0 v) i1 v)` over the base all-zero array, with the
/// payload pointer placed at `payload_off`. Distinct indices make the order
/// semantically irrelevant, but it is fixed so the bytes are stable.
fn storeChain(w: anytype, payload_off: u32) !void {
    var offs: [32]u32 = undefined;
    var n: usize = 0;
    for (frame_out_fields) |f| {
        const base = if (f.off == payload_offset_witnessed) payload_off else f.off;
        var k: u32 = 0;
        while (k < f.size) : (k += 1) {
            offs[n] = base + k;
            n += 1;
        }
    }
    var i: usize = 0;
    while (i < n) : (i += 1) try w.writeAll("(store ");
    try w.writeAll("((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00)");
    i = 0;
    while (i < n) : (i += 1) try w.print(" #x{X:0>8} #xAA)", .{offs[i]});
}

/// Build the SMT-LIB text for VC `i`. Caller frees.
pub fn textFor(alloc: Allocator, i: usize) ![]u8 {
    var out = std.io.Writer.Allocating.init(alloc);
    errdefer out.deinit();
    const w = &out.writer;
    const v = vcs[i];

    switch (i) {
        // ── V1 no underflow in `buf.len - 12` ───────────────────────────────
        0 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try w.writeAll("(assert (bvule #x0000000c buf_len))\n");
            try w.writeAll("(assert (not (bvule #x0000000c buf_len)))\n");
            try w.writeAll("(check-sat)\n");
        },
        1 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try w.writeAll("(assert (not (bvule #x0000000c buf_len)))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V2 the payload slice is in bounds ───────────────────────────────
        2 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try decl(w, "length", 32);
            try w.writeAll("(assert (bvule #x0000000c buf_len))\n");
            try w.writeAll("(assert (bvule length (bvsub buf_len #x0000000c)))\n");
            try w.writeAll("(assert (not (bvule (bvadd #x0000000c length) buf_len)))\n");
            try w.writeAll("(check-sat)\n");
        },
        3 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try decl(w, "length", 32);
            try w.writeAll("(assert (bvule #x0000000c buf_len))\n");
            try w.writeAll("(assert (not (bvule (bvadd #x0000000c length) buf_len)))\n");
            try w.writeAll("(check-sat)\n");
        },
        4 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try decl(w, "length", 32);
            try w.writeAll("(assert (bvule #x0000000c buf_len))\n");
            try w.writeAll("(assert (bvule length (bvadd (bvsub buf_len #x0000000c) #x00000001)))\n");
            try w.writeAll("(assert (not (bvule (bvadd #x0000000c length) buf_len)))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V3 @intCast of a usize slice length into u32 fits ───────────────
        5 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len_usize", 64);
            try w.writeAll("(assert (bvule #x000000000000000c buf_len_usize))\n");
            try w.writeAll("(assert (bvule buf_len_usize #x00000000ffffffff))\n");
            try w.writeAll("(assert (not (bvule (bvsub buf_len_usize #x000000000000000c) #x00000000ffffffff)))\n");
            try w.writeAll("(check-sat)\n");
        },
        6 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len_usize", 64);
            try w.writeAll("(assert (not (bvule (bvsub buf_len_usize #x000000000000000c) #x00000000ffffffff)))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V4 MaxPlus step bound for the CRC loop ──────────────────────────
        7 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "steps", 32);
            try decl(w, "payload_len", 32);
            try w.writeAll("(assert (bvule payload_len #x0000ffff))\n");
            try w.writeAll("(assert (bvule steps (bvadd (bvmul #x00000008 payload_len) #x0000000c)))\n");
            try w.writeAll("(assert (not (bvule steps (bvadd (bvmul #x00000008 #x0000ffff) #x0000000c))))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V5 the magic's endianness ───────────────────────────────────────
        8 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "byte0", 8);
            try decl(w, "byte1", 8);
            try w.writeAll("(assert (= byte0 #x41))\n");
            try w.writeAll("(assert (= byte1 #x54))\n");
            try w.writeAll("(assert (not (= (bvor (concat #x00 byte0) (bvshl (concat #x00 byte1) #x0008)) #x5441)))\n");
            try w.writeAll("(check-sat)\n");
        },
        9 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "byte0", 8);
            try decl(w, "byte1", 8);
            try w.writeAll("(assert (= byte0 #x41))\n");
            try w.writeAll("(assert (= byte1 #x54))\n");
            try w.writeAll("(assert (= (bvor (concat #x00 byte0) (bvshl (concat #x00 byte1) #x0008)) #x4154))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V6 padding bytes are zero after zeroBytes + field writes ────────
        10, 11 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_ABV)\n");
            const payload_off = if (i == 10) payload_offset_witnessed else payload_offset_drifted;
            try w.writeAll("(define-fun S () (Array (_ BitVec 32) (_ BitVec 8))\n  ");
            try storeChain(w, payload_off);
            try w.writeAll(")\n");
            try w.writeAll("(assert (not (and");
            for (pad_bytes_64) |b| {
                try w.print("\n  (= (select S #x{X:0>8}) #x00)", .{b});
            }
            try w.writeAll(")))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V7 postcondition: on success payload_len <= in_len - 12 ─────────
        12 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try decl(w, "length", 32);
            try w.writeAll("(assert (bvule #x0000000c buf_len))\n");
            try w.writeAll("(assert (not (=> (and (bvule #x0000000c buf_len) (bvule length (bvsub buf_len #x0000000c))) " ++
                "(bvule (ite (and (bvule #x0000000c buf_len) (bvule length (bvsub buf_len #x0000000c))) length #x00000000) " ++
                "(bvsub buf_len #x0000000c)))))\n");
            try w.writeAll("(check-sat)\n");
        },
        // ── V8 vacuity: the precondition must be satisfiable ────────────────
        13 => {
            try header(w, v);
            try w.writeAll("(set-logic QF_BV)\n");
            try decl(w, "buf_len", 32);
            try w.writeAll("(assert (and (bvule #x0000000c buf_len) (bvule buf_len #xffffffff)))\n");
            try w.writeAll("(check-sat)\n");
        },
        else => unreachable,
    }

    return out.toOwnedSlice();
}

/// Write every query into `dir` (which must exist). Returns the count.
pub fn generate(alloc: Allocator, dir: std.fs.Dir) !usize {
    for (vcs, 0..) |v, i| {
        const text = try textFor(alloc, i);
        defer alloc.free(text);
        var name_buf: [64]u8 = undefined;
        const name = try std.fmt.bufPrint(&name_buf, "{s}.smt2", .{v.name});
        var f = try dir.createFile(name, .{});
        defer f.close();
        try f.writeAll(text);
    }
    return vcs.len;
}

/// Print the manifest (`name<TAB>expected`) that `verify.sh` diffs against the
/// reviewed `vc/expected.tsv`.
pub fn writeManifest(w: anytype) !void {
    try w.writeAll("# name\texpected\n");
    for (vcs) |v| try w.print("{s}\t{s}\n", .{ v.name, v.expected.name() });
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

const testing = std.testing;

test "the contract binding rejects a drifted contract" {
    const good =
        \\cspec 1
        \\requires ( <= 12 ( len input ) )
        \\requires ( < input_len 4294967296 )
        \\ensures ( => ( = res 0 ) ( = ( magic out ) 21569 ) )
        \\ensures ( => ( = res 0 ) ( <= ( payload_len out ) ( - ( len input ) 12 ) ) )
        \\bound steps ( + 12 ( * 8 input_len ) )
        \\
    ;
    try checkContract(good);
    const drifted =
        \\cspec 1
        \\requires ( <= 11 ( len input ) )
        \\requires ( < input_len 4294967296 )
        \\ensures ( => ( = res 0 ) ( = ( magic out ) 21569 ) )
        \\ensures ( => ( = res 0 ) ( <= ( payload_len out ) ( - ( len input ) 12 ) ) )
        \\bound steps ( + 12 ( * 8 input_len ) )
        \\
    ;
    try testing.expectError(error.ContractDrift, checkContract(drifted));
}

test "the VC set is the reviewed set" {
    try testing.expectEqual(@as(usize, 14), vcs.len);
    try testing.expectEqualStrings("V1_no_underflow", vcs[0].name);
    try testing.expectEqualStrings("V8_premise_satisfiable", vcs[13].name);
}

test "every query is ASCII, LF-terminated and ends in check-sat" {
    const ta = testing.allocator;
    for (vcs, 0..) |v, i| {
        const text = try textFor(ta, i);
        defer ta.free(text);
        for (text) |c| try testing.expect(c < 0x80);
        try testing.expect(std.mem.endsWith(u8, text, "(check-sat)\n"));
        try testing.expect(std.mem.indexOf(u8, text, v.why) != null);
    }
}

test "generation is deterministic" {
    const ta = testing.allocator;
    for (0..vcs.len) |i| {
        const a = try textFor(ta, i);
        defer ta.free(a);
        const b = try textFor(ta, i);
        defer ta.free(b);
        try testing.expectEqualStrings(a, b);
    }
}

test "the drift query differs from the witnessed one" {
    const ta = testing.allocator;
    const ok = try textFor(ta, 10);
    defer ta.free(ok);
    const drift = try textFor(ta, 11);
    defer ta.free(drift);
    try testing.expect(!std.mem.eql(u8, ok, drift));
    // Offset 12 (0x0C) is a padding hole in the witnessed layout and the
    // payload's first byte in the drifted one: that single difference is the
    // whole content of V6_mutant_offset_drift.
    try testing.expect(std.mem.indexOf(u8, ok, "#x0000000C #xAA") == null);
    try testing.expect(std.mem.indexOf(u8, drift, "#x0000000C #xAA") != null);
}
