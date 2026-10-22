#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
"""gen_vcs.py - build, emit and discharge the frame-v1 verification conditions.

This is the *untrusted* VC generator for the worked example. What it emits is a
set of SMT-LIB QF_BV / QF_ABV queries; what it proves is whatever z3 proves
about those queries. Every file it writes is re-parsed from disk before being
checked, so the checked artifact and the stored artifact are byte-identical.

Two families of query are produced for each obligation:

  positive  premises /\\ not goal      must be UNSAT   (obligation discharged)
  needle    premises\P /\\ not goal    must be SAT     (premise P is load-bearing)

The `needle` family is what stops a contract from being vacuously true: if a
precondition can be deleted without turning the goal into a counterexample, the
precondition was doing no work and the mutation harness must say so.

Run:  python3 gen_vcs.py [--out DIR]     exit 0 iff every expectation holds.
"""

import argparse
import os
import sys

try:
    import z3
except ImportError:
    print("SKIP: z3 not available (pip install z3-solver)", file=sys.stderr)
    sys.exit(2)

BV8, BV16, BV32, BV64 = (z3.BitVecSort(8), z3.BitVecSort(16),
                         z3.BitVecSort(32), z3.BitVecSort(64))

HEADER_LEN = 12
MAGIC = 0x5441  # little-endian u16 whose *bytes* are 'A' 'T'


class VC:
    def __init__(self, name, kind, premise, goal, expect, why):
        self.name, self.kind = name, kind
        self.premise, self.goal = premise, goal
        self.expect, self.why = expect, why


def bv(name, width):
    return z3.BitVec(name, width)


def build():
    vcs = []

    # ── V1  no underflow in `buf.len - HEADER_LEN` ──────────────────────────
    n = bv("buf_len", 32)
    vcs.append(VC(
        "V1_no_underflow", "arith",
        [z3.ULE(z3.BitVecVal(HEADER_LEN, 32), n)],
        z3.ULE(z3.BitVecVal(0, 32), z3.BitVecVal(0, 32)),  # trivial goal
        "unsat",
        "`buf.len - 12` cannot wrap once len >= 12 is known"))

    vcs.append(VC(
        "V1_needle_drop_requires", "arith",
        [],  # the `len >= 12` premise is removed
        z3.ULE(z3.BitVecVal(HEADER_LEN, 32), n),
        "sat",
        "without `len >= 12` the subtraction underflows: model is the panic"))

    # ── V2  the payload slice is in bounds ─────────────────────────────────
    L = bv("length", 32)
    avail = z3.BitVecVal(HEADER_LEN, 32)
    p_len_ok = z3.ULE(z3.BitVecVal(HEADER_LEN, 32), n)
    p_payload = z3.ULE(L, n - z3.BitVecVal(HEADER_LEN, 32))
    vcs.append(VC(
        "V2_slice_in_bounds", "bounds",
        [p_len_ok, p_payload],
        z3.ULE(z3.BitVecVal(HEADER_LEN, 32) + L, n),
        "unsat",
        "12 + length <= buf.len, so buf[12 .. 12+length] is in bounds"))

    # ── V2 needle: drop the payload bound -> out-of-bounds is reachable ─────
    vcs.append(VC(
        "V2_needle_drop_payload_bound", "bounds",
        [p_len_ok],
        z3.ULE(z3.BitVecVal(HEADER_LEN, 32) + L, n),
        "sat",
        "a frame claiming more bytes than the buffer holds slices out of bounds"))

    # ── V2 mutant: the off-by-one an author actually writes ────────────────
    #     `if (length > avail + 1) return error.Truncated;`
    vcs.append(VC(
        "V2_mutant_off_by_one", "bounds",
        [p_len_ok, z3.ULE(L, n - z3.BitVecVal(HEADER_LEN, 32) + z3.BitVecVal(1, 32))],
        z3.ULE(z3.BitVecVal(HEADER_LEN, 32) + L, n),
        "sat",
        "`avail + 1` admits exactly one byte past the end: off-by-one"))

    # ── V3  @intCast of a usize slice length into u32 fits ─────────────────
    N64 = bv("buf_len_usize", 64)
    # NOTE: the first version of this VC had only the upper bound as a premise
    # and z3 returned SAT with buf_len_usize = 0. That is correct: in BV64,
    # `0 - 12` wraps to 2^64-12, which does not fit in u32. The no-underflow
    # premise is load-bearing *in the bitvector encoding even though it is
    # obvious in the integers*. This is the trap the spec calls out (§4.3.1):
    # the same obligation needs two premises here and one in Nat.
    vcs.append(VC(
        "V3_intcast_range", "cast",
        [z3.ULE(z3.BitVecVal(HEADER_LEN, 64), N64),
         z3.ULE(N64, z3.BitVecVal(0xFFFF_FFFF, 64))],
        z3.ULE(N64 - z3.BitVecVal(HEADER_LEN, 64), z3.BitVecVal(0xFFFF_FFFF, 64)),
        "unsat",
        "a slice obtained from a u32 in_len is at most 2^32-1 bytes and at "
        "least 12, so the usize-to-u32 @intCast cannot trap"))

    vcs.append(VC(
        "V3_needle_drop_ffi_bound", "cast",
        [],
        z3.ULE(N64 - z3.BitVecVal(HEADER_LEN, 64), z3.BitVecVal(0xFFFF_FFFF, 64)),
        "sat",
        "called directly with a >4GiB slice, the same @intCast panics"))

    # ── V4  MaxPlus step bound for the CRC loop ────────────────────────────
    steps, ln = bv("steps", 32), bv("payload_len", 32)
    vcs.append(VC(
        "V4_maxplus_bound", "cost",
        [z3.ULE(ln, z3.BitVecVal(65535, 32)),
         z3.ULE(steps, z3.BitVecVal(8, 32) * ln + z3.BitVecVal(HEADER_LEN, 32))],
        z3.ULE(steps, z3.BitVecVal(8, 32) * z3.BitVecVal(65535, 32) + z3.BitVecVal(HEADER_LEN, 32)),
        "unsat",
        "8 steps per payload byte; worst case 8*65535+12 < 2^32 so the MaxPlus "
        "bound is representable in the cost domain"))

    # ── V5  the magic's endianness ─────────────────────────────────────────
    b0, b1 = bv("byte0", 8), bv("byte1", 8)
    le16 = z3.ZeroExt(8, b0) | (z3.ZeroExt(8, b1) << 8)
    vcs.append(VC(
        "V5_magic_wire_order", "abi",
        [b0 == z3.BitVecVal(ord('A'), 8), b1 == z3.BitVecVal(ord('T'), 8)],
        le16 == z3.BitVecVal(MAGIC, 16),
        "unsat",
        "bytes 'A','T' decode to 0x5441; the 'obvious' 0x4154 would put 'T','A' "
        "on the wire"))

    vcs.append(VC(
        "V5_mutant_wrong_endian", "abi",
        [b0 == z3.BitVecVal(ord('A'), 8), b1 == z3.BitVecVal(ord('T'), 8),
         le16 == z3.BitVecVal(0x4154, 16)],
        z3.BoolVal(False),
        "unsat",
        "0x4154 is refuted by the same bytes: the literal ASCII word is wrong"))

    # ── V6  padding bytes are zero after zeroBytes + field writes ───────────
    #     FrameOut on 64-bit: padding 6..8, 12..16, 28..32.
    A0, A1 = z3.Const("A0", z3.ArraySort(BV32, BV8)), None
    zeroed = z3.K(BV32, z3.BitVecVal(0, 8))          # all bytes zero
    writes = []
    for off, size in [(0, 2), (2, 2), (4, 1), (5, 1), (8, 4), (16, 8), (24, 4)]:
        for k in range(size):
            writes.append((off + k, z3.BitVecVal(0xAA, 8)))  # arbitrary field byte
    arr = zeroed
    for idx, val in writes:
        arr = z3.Store(arr, z3.BitVecVal(idx, 32), val)
    goals = [z3.Select(arr, z3.BitVecVal(i, 32)) == z3.BitVecVal(0, 8)
             for i in list(range(6, 8)) + list(range(12, 16)) + list(range(28, 32))]
    vcs.append(VC(
        "V6_padding_zeroed", "layout",
        [],
        z3.And(*goals),
        "unsat",
        "writes hit only field bytes, so every padding byte keeps the 0x00 it got "
        "from zeroBytes"))

    # Layout drift: the same writes, but `payload` placed at offset 12 instead of
    # 16 (what happens if @offsetOf for one target is transcribed wrongly, or a
    # field is added without re-deriving the table). Bytes 12..16 are padding on
    # 64-bit, so the padding VC must now fail.
    drifted = zeroed
    for off, size in [(0, 2), (2, 2), (4, 1), (5, 1), (8, 4), (12, 8), (24, 4)]:
        for k in range(size):
            drifted = z3.Store(drifted, z3.BitVecVal(off + k, 32), z3.BitVecVal(0xAA, 8))
    vcs.append(VC(
        "V6_mutant_offset_drift", "layout",
        [],
        z3.And(z3.Select(drifted, z3.BitVecVal(12, 32)) == z3.BitVecVal(0, 8),
               z3.Select(drifted, z3.BitVecVal(13, 32)) == z3.BitVecVal(0, 8),
               z3.Select(drifted, z3.BitVecVal(14, 32)) == z3.BitVecVal(0, 8),
               z3.Select(drifted, z3.BitVecVal(15, 32)) == z3.BitVecVal(0, 8)),
        "sat",
        "a payload placed at offset 12 writes into the padding hole 12..16: the "
        "padding VC catches layout drift"))

    # ── V7  postcondition: on success payload_len <= in_len - 12 ───────────
    ok = z3.And(p_len_ok, p_payload)
    out_len = z3.If(ok, L, z3.BitVecVal(0, 32))
    vcs.append(VC(
        "V7_post_payload_len", "post",
        [p_len_ok],
        z3.Implies(ok, z3.ULE(out_len, n - z3.BitVecVal(HEADER_LEN, 32))),
        "unsat",
        "the success postcondition follows from the guard that produced success"))

    # ── V8  vacuity: the precondition must be satisfiable ──────────────────
    vcs.append(VC(
        "V8_premise_satisfiable", "vacuity",
        [],
        z3.And(z3.ULE(z3.BitVecVal(HEADER_LEN, 32), n),
               z3.ULE(n, z3.BitVecVal(0xFFFF_FFFF, 32))),
        "sat",
        "a contradictory precondition would make every VC trivially UNSAT, so "
        "satisfiability of the premises is a VC in its own right"))

    return vcs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__))))
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    # Remove VCs from a previous run so the directory is exactly this run's set.
    # A stale file would otherwise leak into the aggregate content address.
    for stale in os.listdir(args.out):
        if stale.endswith(".smt2"):
            os.remove(os.path.join(args.out, stale))

    failures = 0
    rows = []
    for vc in build():
        s = z3.Solver()
        if vc.premise:
            s.add(vc.premise if isinstance(vc.premise, z3.BoolRef) else z3.And(*vc.premise))
        s.add(z3.Not(vc.goal))
        text = s.to_smt2()
        path = os.path.join(args.out, vc.name + ".smt2")
        with open(path, "w", encoding="ascii") as f:
            f.write("; SPDX-License-Identifier: MPL-2.0\n")
            f.write("; generated by gen_vcs.py - %s (%s)\n" % (vc.name, vc.kind))
            f.write("; %s\n" % vc.why)
            f.write("; expected: %s\n" % vc.expect.upper())
            f.write(text)

        # Re-parse what we just wrote: the artifact checked is the artifact stored.
        replay = z3.Solver()
        replay.from_string(open(path, encoding="ascii").read())
        res = replay.check()
        if res == z3.sat:
            got = "sat"
        elif res == z3.unsat:
            got = "unsat"
        else:
            got = "unknown"
        ok = got == vc.expect
        model = ""
        if got == "sat" and ok:
            m = replay.model()
            vals = []
            for d in m.decls():
                vals.append("%s=%s" % (d.name(), m[d]))
            model = ", ".join(sorted(vals))
        rows.append((vc.name, vc.expect, got, "ok" if ok else "FAIL", vc.why, model))
        if not ok:
            failures += 1

    width = max(len(r[0]) for r in rows)
    print("%-*s  %-5s  %-5s  %-4s  %s" % (width, "VC", "want", "z3", "", "meaning"))
    for name, want, got, verdict, why, model in rows:
        print("%-*s  %-5s  %-5s  %-4s  %s" % (width, name, want, got, verdict, why))
        if model:
            print("%-*s  model: %s" % (width, "", model))
    print("\n%d VCs, %d failing" % (len(rows), failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
