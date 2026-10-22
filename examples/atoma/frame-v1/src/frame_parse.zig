// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// frame_parse.zig — worked example for the Atoma specification.
//
// A length-prefixed, CRC-protected frame is validated in place and described by
// a C-ABI `extern struct` that points back into the caller's buffer (zero copy).
//
// Wire format v1 (little endian):
//
//   off  size  field      meaning
//   0    2     magic      bytes 0x41 0x54, i.e. 'A' then 'T' on the wire
//                        (little-endian u16 value 0x5441 — NOT 0x4154)
//   2    2     length     payload byte count, 0..65535
//   4    1     flags      bit 0 = compressed; all other bits must be 0
//   5    1     tag        application tag, opaque to Atoma
//   6    4     crc32      IEEE CRC-32 over header[0..6] ++ payload
//   10   2     reserved   must be 0
//   12   len   payload    length bytes
//
// The contract is in abi/FrameAbi.idr (Face A) and in the `//!` directive
// blocks on each export fn below (Face B, extracted by `atoma extract`); both
// elaborate to the same canonical Core Spec IR (spec §2.5). This file is what
// the VC generator consumes.
//
// Subset markers used below:
//   //! @requires   pre-condition on the *C* caller (external assumption)
//   //! @ensures    post-condition
//   //! @cap        capability footprint (MPR)
//   //! @frame      what may be written
//   //! @decreases  termination measure / MaxPlus bound

const std = @import("std");
const atoma = @import("atoma.zig");

// ─────────────────────────────────────────────────────────────────────────────
// ABI types — every one of these is `extern` and fixed-width. No `usize`, no
// `bool`, no slices, no packed structs: their layout is target-dependent or not
// C-ABI-stable, and Atoma rejects them at the seam (§2.3).
// ─────────────────────────────────────────────────────────────────────────────

/// Wire magic. The *bytes* matter, not the number: `le16` reads p[0] | p[1]<<8,
/// so the u16 value whose encoding is 'A' 'T' is 0x5441. Writing 0x4154 here
/// would put 'T' 'A' in the first two bytes of every frame. `test "wire order"`
/// pins this down.
pub const MAGIC: u16 = 0x5441;
pub const HEADER_LEN: u32 = 12;
pub const FLAG_COMPRESSED: u8 = 0x01;
/// In-memory capability tag, ASCII "ATM1" read big-endian. Never serialised, so
/// there is no wire-order question: it is compared as a number.
pub const HANDLE_TAG: u32 = 0x41544D31;
pub const MAX_ITERS: u32 = 4;

/// C-visible result codes. `enum(c_int)` is C-ABI safe; a bare Zig `error` union
/// is not, so errors are translated at the shell (see `mapError`).
pub const Result = enum(c_int) {
    ok = 0,
    invalid_arg = 1,
    truncated = 2,
    bad_magic = 3,
    bad_flags = 4,
    bad_reserved = 5,
    bad_crc = 6,
    no_space = 7,
    busy = 8,
};

/// Library handle: an opaque capability token plus the iterator lease table.
/// There is no allocator anywhere in this module (MPR: the only authority is the
/// handle the caller passed in).
pub const Handle = extern struct {
    abi_tag: u32,
    abi_version: u32,
    /// Bit i is set iff `iters[i]` is live.
    live: u32,
    iters: [MAX_ITERS]FrameIter,
};

/// Parsed header view. Layout is target-independent (all fields fixed-width).
pub const FrameHeader = extern struct {
    magic: u16, // 0
    length: u16, // 2
    flags: u8, // 4
    tag: u8, // 5
    // padding 6..8
    crc: u32, // 8
    reserved: u16, // 12
    // padding 14..16
};

/// Parse output. Contains a pointer, so its layout is proven *per target triple*:
///   x86_64/aarch64/riscv64: size 32, align 8, payload@16, payload_len@24,
///                           padding 6..8, 12..16, 28..32
///   wasm32:                 size 20, align 4, payload@12, payload_len@16,
///                           padding 6..8
pub const FrameOut = extern struct {
    magic: u16, // 0
    length: u16, // 2
    flags: u8, // 4
    tag: u8, // 5
    // padding 6..8
    crc: u32, // 8
    payload: [*]const u8, // 16 | 12
    payload_len: u32, // 24 | 16
    // padding 28..32 (and 12..16 before the pointer) on 64-bit targets
};

/// Zero-copy iterator state. Lives in a slot leased from `Handle`.
pub const FrameIter = extern struct {
    buf: [*]const u8,
    len: u32,
    cursor: u32,
    frames: u32,
};

const ParseError = error{ Truncated, BadMagic, BadFlags, BadReserved, BadCrc };

// ─────────────────────────────────────────────────────────────────────────────
// Little-endian readers. Written as explicit byte indices rather than
// `std.mem.readInt` so that every load carries an obvious bounds obligation:
// each `p[i]` with i < HEADER_LEN is justified by `buf.len >= HEADER_LEN`.
// ─────────────────────────────────────────────────────────────────────────────

inline fn le16(p: [*]const u8, off: u32) u16 {
    return @as(u16, p[off]) | (@as(u16, p[off + 1]) << 8);
}

inline fn le32(p: [*]const u8, off: u32) u32 {
    return @as(u32, p[off]) |
        (@as(u32, p[off + 1]) << 8) |
        (@as(u32, p[off + 2]) << 16) |
        (@as(u32, p[off + 3]) << 24);
}

/// IEEE CRC-32, bitwise, no table, no allocation.
/// Termination: the outer loop decreases `bytes.len - i`; the inner loop is the
/// constant 8. MaxPlus cost = 8 * bytes.len + 3 steps.
fn crc32(bytes: []const u8) u32 {
    return ~crc32Update(0xFFFF_FFFF, bytes);
}

/// Raw (un-finalised) CRC state update. `crc32Update(0xFFFF_FFFF, b)` followed by
/// `~` is the IEEE CRC-32 of `b`.
fn crc32Update(prev: u32, bytes: []const u8) u32 {
    var c: u32 = prev;
    for (bytes) |b| {
        c ^= b;
        var k: u8 = 0;
        while (k < 8) : (k += 1) { // @decreases (8 - k) ; MaxPlus step = 8
            c = if (c & 1 != 0) (c >> 1) ^ 0xEDB8_8320 else c >> 1;
        }
    }
    return c;
}

// ─────────────────────────────────────────────────────────────────────────────
// Core parser. This is the verified function: total on every input whose length
// precondition holds, and it never traps (spec §8.3, VCs V1..V7).
// ─────────────────────────────────────────────────────────────────────────────

/// //! @requires  buf.len >= 12
/// //! @requires  buf.ptr points to buf.len readable bytes (the FFI ghost length)
/// //! @ensures   on error: *out is all-zero (no partial frame, no secret leak)
/// //! @ensures   on success:
/// //!              out.magic = 0x5441
/// //!              out.length = length (bytes 2..4 of buf)
/// //!              out.payload = buf.ptr + 12
/// //!              out.payload_len = out.length
/// //!              out.crc = crc32(buf[0..6] ++ buf[12..12+length])
/// //!              padding(*out) = 0
/// //! @cap       { Read(buf) }
/// //! @frame     *out
fn parseInto(buf: []const u8, out: *FrameOut) ParseError!void {
    // Runs on every error return, and on no success return. The linear
    // obligation is: exactly one of {`errdefer` body, success epilogue} runs.
    // @linear: this handler consumes the partial frame on every error path
    errdefer atoma.zeroBytes(out);

    if (buf.len < HEADER_LEN) return error.Truncated;

    const magic = le16(buf.ptr, 0);
    if (magic != MAGIC) return error.BadMagic;

    const length: u32 = le16(buf.ptr, 2);
    const flags = buf[4];
    if (flags & ~FLAG_COMPRESSED != 0) return error.BadFlags;

    const reserved = le16(buf.ptr, 10);
    if (reserved != 0) return error.BadReserved;

    // @assert: the load-bearing bound. `buf.len >= 12` was established above, so the
    // subtraction cannot wrap; `length <= avail` makes the payload slice total.
    const avail: u32 = @intCast(buf.len - HEADER_LEN);
    if (length > avail) return error.Truncated;

    const payload = buf[HEADER_LEN .. HEADER_LEN + length];
    const want = le32(buf.ptr, 6);
    const c = crc32Update(crc32Update(0xFFFF_FFFF, buf[0..6]), payload);
    if (~c != want) return error.BadCrc;

    // Define every byte first — including padding — then write the fields.
    // `out.* = .{...}` alone would leave 6..8 (and 28..32) undefined.
    atoma.zeroBytes(out);
    out.magic = magic;
    out.length = @intCast(length);
    out.flags = flags;
    out.tag = buf[5];
    out.crc = want;
    out.payload = buf.ptr + HEADER_LEN;
    out.payload_len = length;
}

fn mapError(e: ParseError) Result {
    return switch (e) {
        error.Truncated => .truncated,
        error.BadMagic => .bad_magic,
        error.BadFlags => .bad_flags,
        error.BadReserved => .bad_reserved,
        error.BadCrc => .bad_crc,
    };
}

// ─────────────────────────────────────────────────────────────────────────────
// C ABI shell. Untrusted with respect to the proofs: it only checks pointer
// non-nullity and translates errors. Every `?` unwrap is discharged by the
// orelse, so there is no `.?` anywhere (§2.4).
// ─────────────────────────────────────────────────────────────────────────────

/// @contract atoma.frame.parse
/// @kind extern
/// @param h W handle
/// @param input W slice ro u8 r0
/// @param input_len 0 u32
/// @param out 1 ptr out_frame r1
/// @borrow input shr r0
/// @borrow out mut r1
/// @requires ( <= 12 ( len input ) )
/// @requires ( = ( len input ) input_len )
/// @requires ( < input_len 0x100000000 )
/// @requires ( or ( = h null ) ( = ( tag h ) 0x41544D31 ) )
/// @ensures ( => ( = res 0 ) ( = ( magic out ) 0x5441 ) )
/// @ensures ( => ( = res 0 ) ( <= ( payload_len out ) ( - ( len input ) 12 ) ) )
/// @ensures ( => ( != res 0 ) ( zeroed out ) )
/// @ensures ( = ( pad out ) 0 )
/// @assigns r1
/// @cap Write r1
/// @cap Read r0
/// @bound steps ( + 12 ( * 8 input_len ) )
/// @bound hwm 64
///
/// The contract above is the *only* place the boundary is specified. It is
/// extracted by `atoma extract src/frame_parse.zig` and must hash equal to
/// `spec/face-b.cspec` (gate G8), which in turn must hash equal to the Idris2
/// face (gate G5). Three sources of truth, one digest.
export fn atoma_frame_parse(
    h: ?*const Handle,
    in_ptr: ?[*]const u8,
    in_len: u32,
    out: ?*FrameOut,
) callconv(.c) Result {
    const handle = h orelse return .invalid_arg;
    if (handle.abi_tag != HANDLE_TAG) return .invalid_arg;
    const p = in_ptr orelse return .invalid_arg;
    const dst = out orelse return .invalid_arg;

    parseInto(p[0..in_len], dst) catch |e| return mapError(e);
    return .ok;
}

// ── handle lifecycle ────────────────────────────────────────────────────────

/// @contract atoma.handle.create
/// @kind extern
/// @param out 1 ptr out_handle r0
/// @requires ( = ( len out ) 64 )
/// @requires ( = ( align out ) 8 )
/// @ensures ( = ( tag out ) 0x41544D31 )
/// @ensures ( = ( live out ) 0 )
/// @ensures ( = ( pad out ) 0 )
/// @assigns r0
/// @cap Write r0
/// @bound steps 4
/// @bound hwm 32
///
/// `out` is a caller-owned lease: the callee writes and returns, it does not
/// retain the pointer.
export fn atoma_handle_create(out: ?*Handle) callconv(.c) Result {
    const h = out orelse return .invalid_arg;
    atoma.zeroBytes(h);
    h.abi_tag = HANDLE_TAG;
    h.abi_version = 1;
    return .ok;
}

/// @contract atoma.handle.destroy
/// @kind extern
/// @param h 1 ptr inout_handle r0
/// @requires ( = ( tag h ) 0x41544D31 )
/// @requires ( = ( live h ) 0 )
/// @ensures ( = ( zeroed h ) 1 )
/// @assigns r0
/// @cap Write r0
/// @bound steps 3
/// @bound hwm 16
///
/// Refuses with `.busy` while any iterator lease is live, so a leaked linear
/// lease surfaces as a refused destroy rather than as a use-after-free.
export fn atoma_handle_destroy(h: ?*Handle) callconv(.c) Result {
    const hh = h orelse return .invalid_arg;
    if (hh.abi_tag != HANDLE_TAG) return .invalid_arg;
    if (hh.live != 0) return .busy; // a leaked linear lease is refused
    atoma.zeroBytes(hh);
    return .ok;
}

// ── linear iterator: open → next* → close ───────────────────────────────────

/// @contract atoma.iter.open
/// @kind extern
/// @param h 1 ptr inout_handle r0
/// @param input W slice ro u8 r1
/// @param input_len 0 u32
/// @param out 1 ptr out_iter r2
/// @requires ( < ( popcount ( live h ) ) 4 )
/// @requires ( = ( len input ) input_len )
/// @ensures ( => ( = res 0 ) ( = ( popcount ( live h ) ) ( + 1 ( popcount_old ( live h ) ) ) ) )
/// @assigns r0
/// @cap Write r0
/// @cap Read r1
/// @bound steps 8
/// @bound hwm 48
///
/// Linear: a successful open creates exactly one lease, and `atoma_iter_close`
/// is the only operation that consumes it.
export fn atoma_iter_open(
    h: ?*Handle,
    in_ptr: ?[*]const u8,
    in_len: u32,
    out: ?*?*FrameIter,
) callconv(.c) Result {
    const hh = h orelse return .invalid_arg;
    if (hh.abi_tag != HANDLE_TAG) return .invalid_arg;
    const p = in_ptr orelse return .invalid_arg;
    const slot_out = out orelse return .invalid_arg;

    var i: u32 = 0;
    while (i < MAX_ITERS) : (i += 1) {
        if (hh.live & (@as(u32, 1) << @intCast(i)) == 0) {
            hh.iters[i] = .{ .buf = p, .len = in_len, .cursor = 0, .frames = 0 };
            hh.live |= @as(u32, 1) << @intCast(i);
            slot_out.* = &hh.iters[i];
            return .ok;
        }
    }
    return .no_space;
}

/// @contract atoma.iter.next
/// @kind extern
/// @param it 1 ptr inout_iter r0
/// @param out 1 ptr out_frame r1
/// @requires ( <= ( cursor it ) ( len it ) )
/// @ensures ( => ( = res 0 ) ( <= ( + ( cursor_old it ) 12 ( payload_len out ) ) ( len it ) ) )
/// @ensures ( => ( != res 0 ) ( zeroed out ) )
/// @ensures ( = ( pad out ) 0 )
/// @assigns r0
/// @assigns r1
/// @cap Read r0
/// @cap Write r1
/// @bound steps ( + 32 ( * 8 ( len it ) ) )
/// @bound hwm 96
///
/// The cursor advance is the only state change, and it is bounded by the
/// payload-length postcondition because `parseInto` succeeded.
export fn atoma_iter_next(it: ?*FrameIter, out: ?*FrameOut) callconv(.c) Result {
    const s = it orelse return .invalid_arg;
    const dst = out orelse return .invalid_arg;

    const remaining = s.len - s.cursor; // cursor ≤ len is an invariant (VC I3)
    if (remaining < HEADER_LEN) return .truncated;

    const base = s.buf + s.cursor;
    const sub = base[0..remaining];
    parseInto(sub, dst) catch |e| return mapError(e);

    s.cursor += HEADER_LEN + dst.payload_len; // proven ≤ len because parse succeeded
    s.frames += 1;
    return .ok;
}

/// @contract atoma.iter.close
/// @kind extern
/// @param h 1 ptr inout_handle r0
/// @param it 1 ptr inout_iter r1
/// @requires ( = ( owns h it ) 1 )
/// @ensures ( = ( live h ) ( clear_bit ( live_old h ) ( index_of h it ) ) )
/// @ensures ( = ( zeroed it ) 1 )
/// @assigns r0
/// @assigns r1
/// @cap Write r0
/// @cap Write r1
/// @bound steps 8
/// @bound hwm 32
///
/// Consumes the lease exactly once; the `live` bit is cleared before the slot is
/// wiped, so a concurrent observer can never see a live bit over zeroed state.
export fn atoma_iter_close(h: ?*Handle, it: ?*FrameIter) callconv(.c) Result {
    const hh = h orelse return .invalid_arg;
    if (hh.abi_tag != HANDLE_TAG) return .invalid_arg;
    const s = it orelse return .invalid_arg;

    var i: u32 = 0;
    while (i < MAX_ITERS) : (i += 1) {
        if (&hh.iters[i] == s) {
            if (hh.live & (@as(u32, 1) << @intCast(i)) == 0) return .invalid_arg;
            hh.live &= ~(@as(u32, 1) << @intCast(i));
            atoma.zeroBytes(&hh.iters[i]);
            return .ok;
        }
    }
    return .invalid_arg;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests. These are the *witnesses* the mutation harness uses: a mutant that
// still passes this suite has escaped both the proofs and the tests.
// ─────────────────────────────────────────────────────────────────────────────

const testing = std.testing;

fn buildFrame(buf: []u8, tag: u8, payload: []const u8) usize {
    const n: u16 = @intCast(payload.len);
    buf[0] = @truncate(MAGIC);
    buf[1] = @truncate(MAGIC >> 8);
    buf[2] = @truncate(n);
    buf[3] = @truncate(n >> 8);
    buf[4] = 0;
    buf[5] = tag;
    buf[10] = 0;
    buf[11] = 0;
    @memcpy(buf[HEADER_LEN .. HEADER_LEN + payload.len], payload);
    var c = std.hash.Crc32.init();
    c.update(buf[0..6]);
    c.update(payload);
    const v = c.final();
    buf[6] = @truncate(v);
    buf[7] = @truncate(v >> 8);
    buf[8] = @truncate(v >> 16);
    buf[9] = @truncate(v >> 24);
    return HEADER_LEN + payload.len;
}

test "parses a well-formed frame, zero-copy" {
    var buf: [64]u8 = undefined;
    const n = buildFrame(&buf, 7, "hello");
    var h: Handle = undefined;
    try testing.expectEqual(Result.ok, atoma_handle_create(&h));
    var out: FrameOut = undefined;
    try testing.expectEqual(Result.ok, atoma_frame_parse(&h, &buf, @intCast(n), &out));
    try testing.expectEqual(MAGIC, out.magic);
    try testing.expectEqual(@as(u32, 5), out.payload_len);
    try testing.expectEqual(@as(u8, 7), out.tag);
    // zero-copy: the payload pointer aliases the caller's buffer
    try testing.expectEqual(@intFromPtr(&buf[HEADER_LEN]), @intFromPtr(out.payload));
    try testing.expect(atoma.paddingIsZero(&out));
}

test "rejects a short buffer without touching out" {
    var buf: [4]u8 = .{ 0, 0, 0, 0 };
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var out: FrameOut = undefined;
    atoma.zeroBytes(&out);
    try testing.expectEqual(Result.truncated, atoma_frame_parse(&h, &buf, buf.len, &out));
    try testing.expect(atoma.isZeroed(&out));
}

test "length == avail is accepted, length == avail+1 is rejected" {
    var buf: [64]u8 = undefined;
    const n = buildFrame(&buf, 1, "abc");
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var out: FrameOut = undefined;
    // exact fit
    try testing.expectEqual(Result.ok, atoma_frame_parse(&h, &buf, @intCast(n), &out));
    // claim one byte more than the buffer holds
    buf[2] = 4;
    try testing.expectEqual(Result.truncated, atoma_frame_parse(&h, &buf, @intCast(n), &out));
    try testing.expect(atoma.isZeroed(&out)); // errdefer ran
}

test "bad magic, flags and reserved are refused" {
    var buf: [64]u8 = undefined;
    const n = buildFrame(&buf, 1, "x");
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var out: FrameOut = undefined;
    buf[0] = 0;
    try testing.expectEqual(Result.bad_magic, atoma_frame_parse(&h, &buf, @intCast(n), &out));
    _ = buildFrame(&buf, 1, "x");
    buf[4] = 0x80;
    try testing.expectEqual(Result.bad_flags, atoma_frame_parse(&h, &buf, @intCast(n), &out));
    _ = buildFrame(&buf, 1, "x");
    buf[10] = 0xFF;
    try testing.expectEqual(Result.bad_reserved, atoma_frame_parse(&h, &buf, @intCast(n), &out));
}

test "crc mismatch is caught" {
    var buf: [64]u8 = undefined;
    const n = buildFrame(&buf, 1, "xyz");
    buf[HEADER_LEN] ^= 0xFF;
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var out: FrameOut = undefined;
    try testing.expectEqual(Result.bad_crc, atoma_frame_parse(&h, &buf, @intCast(n), &out));
}

test "null arguments are refused, every one of them" {
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var out: FrameOut = undefined;
    var buf: [16]u8 = [_]u8{0} ** 16;
    try testing.expectEqual(Result.invalid_arg, atoma_frame_parse(null, &buf, 16, &out));
    try testing.expectEqual(Result.invalid_arg, atoma_frame_parse(&h, null, 16, &out));
    try testing.expectEqual(Result.invalid_arg, atoma_frame_parse(&h, &buf, 16, null));
}

test "iterator leases are linear: leak is detected, close releases" {
    var buf: [64]u8 = undefined;
    const n = buildFrame(&buf, 2, "ab");
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var p: ?*FrameIter = null;
    try testing.expectEqual(Result.ok, atoma_iter_open(&h, &buf, @intCast(n), &p));
    var out: FrameOut = undefined;
    try testing.expectEqual(Result.ok, atoma_iter_next(p, &out));
    try testing.expectEqual(@as(u32, 2), out.payload_len);
    // destroy refuses while a lease is live
    try testing.expectEqual(Result.busy, atoma_handle_destroy(&h));
    try testing.expectEqual(Result.ok, atoma_iter_close(&h, p));
    try testing.expectEqual(Result.ok, atoma_handle_destroy(&h));
    try testing.expect(atoma.isZeroed(&h));
}

test "iterator walks consecutive frames and stops at the end" {
    var buf: [128]u8 = undefined;
    const a = buildFrame(&buf, 1, "aa");
    const b = buildFrame(buf[a..], 2, "bbb");
    var h: Handle = undefined;
    _ = atoma_handle_create(&h);
    var p: ?*FrameIter = null;
    try testing.expectEqual(Result.ok, atoma_iter_open(&h, &buf, @intCast(a + b), &p));
    var out: FrameOut = undefined;
    try testing.expectEqual(Result.ok, atoma_iter_next(p, &out));
    try testing.expectEqual(@as(u8, 1), out.tag);
    try testing.expectEqual(Result.ok, atoma_iter_next(p, &out));
    try testing.expectEqual(@as(u8, 2), out.tag);
    try testing.expectEqual(Result.truncated, atoma_iter_next(p, &out));
    try testing.expectEqual(Result.ok, atoma_iter_close(&h, p));
}

test "wire order: the first two bytes are 'A' then 'T'" {
    var buf: [64]u8 = undefined;
    _ = buildFrame(&buf, 0, "x");
    try testing.expectEqual(@as(u8, 'A'), buf[0]);
    try testing.expectEqual(@as(u8, 'T'), buf[1]);
}

test "layout: FrameHeader is target-independent" {
    try testing.expectEqual(@as(usize, 16), @sizeOf(FrameHeader));
    try testing.expectEqual(@as(usize, 4), @alignOf(FrameHeader));
    try testing.expectEqual(@as(usize, 8), @offsetOf(FrameHeader, "crc"));
    try testing.expectEqual(@as(usize, 12), @offsetOf(FrameHeader, "reserved"));
}

test "layout: FrameOut follows the pointer width" {
    if (@sizeOf(usize) == 8) {
        try testing.expectEqual(@as(usize, 32), @sizeOf(FrameOut));
        try testing.expectEqual(@as(usize, 16), @offsetOf(FrameOut, "payload"));
        try testing.expectEqual(@as(usize, 24), @offsetOf(FrameOut, "payload_len"));
    } else {
        try testing.expectEqual(@as(usize, 20), @sizeOf(FrameOut));
        try testing.expectEqual(@as(usize, 12), @offsetOf(FrameOut, "payload"));
        try testing.expectEqual(@as(usize, 16), @offsetOf(FrameOut, "payload_len"));
    }
}
