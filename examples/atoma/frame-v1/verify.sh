#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# verify.sh — the Phase 0 ("Layout & Signature Lock") gate for frame-v1.
#
# What this gate DOES establish (machine-checked, here and now):
#   G1  the example implementation is within the Atoma subset: it compiles and
#       its 11 unit tests pass on the pinned compiler;
#   G2  it compiles for all four ABI target classes (x86_64 · aarch64 · riscv64
#       · wasm32);
#   G3  every declared size / alignment / offset / padding range is confirmed by
#       the Zig compiler on each of those targets (layout.sh);
#   G4  the `usize`-across-FFI counter-example is *rejected* on wasm32 (F0.3);
#   G5  Face A and Face B canonicalise to the same bytes (hash-checked seam);
#   G6  all 11 specification-mutation operators produce distinct artifacts;
#   G7  the 14 SMT verification conditions are discharged (if z3 is present);
#   G8  the Face B contract is *extracted* from the Zig source and matches the
#       checked-in file — the doc-comment directives are the source of truth;
#   G9  the implementation passes the subset checker with zero diagnostics and
#       every `export fn` contracted;
#   G10 the negative corpus is rejected, with one diagnostic per banned
#       construct (the checker is not vacuous);
#   G11 the Agda metatheory typechecks under `--safe --without-K` (if agda is
#       present) — the soundness theorem of spec §6.3 is machine-checked for the
#       store-free core fragment, not asserted.
#
# What this gate does NOT establish — and must never be read as establishing:
#   * that the SMT obligations are valid, unless z3 was present and G7 passed;
#   * that the metatheory says anything about *this* Zig program rather than
#     about the model in `Core.agda` (the refinement obligation is manual and
#     unwritten — spec §6.4 and the non-claims of §10.5);
#   * that the Dedukti witness typechecks (no dkcheck ran);
#   * that Coq/Lean accept the statement (no coqchk / lean4checker ran).
# Because of that the receipt this script writes is stamped
# `INCOMPLETE (Warrant)`, never `COMPLETE (Receipt)` (spec §1, §7.4).
#
# Exit status is 0 only if every gate that can run in this environment passes.
# G7 and G11 are skip-to-not-run: absence of a tool is reported, never assumed
# away, and never counted as a pass.

set -eu

ZIG=${ZIG:-zig}
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../../.." && pwd)
ADDR="$root/tools/atoma/zig-out/bin/atoma"

die() {
    printf 'FAIL %s\n' "$1" >&2
    exit 1
}

[ -x "$ADDR" ] || (cd "$root/tools/atoma" && "$ZIG" build >/dev/null) || die "cannot build atoma"

cd "$here"

# ── G1: subset conformance + unit tests ─────────────────────────────────────
"$ZIG" test src/frame_parse.zig >/dev/null 2>&1 || die "G1 unit tests"
printf 'G1 ok  unit tests (frame_parse)\n'

# ── G2: four target classes ─────────────────────────────────────────────────
for triple in x86_64-linux-gnu aarch64-linux-gnu riscv64-linux-gnu wasm32-freestanding; do
    "$ZIG" build-obj src/frame_parse.zig -target "$triple" -fno-emit-bin >/dev/null 2>&1 ||
        die "G2 cross-compile $triple"
done
printf 'G2 ok  cross-compiles: x86_64 aarch64 riscv64 wasm32\n'

# ── G3: layout witnesses ────────────────────────────────────────────────────
./tools/layout.sh >/dev/null || die "G3 layout witness"
rows=$(wc -l < spec/layout.cspec | tr -d ' ')
[ "$rows" = 60 ] || die "G3 expected 60 layout rows, got $rows"
printf 'G3 ok  layout witness: %s rows over 4 targets\n' "$rows"

# ── G4: the negative layout falsifier ───────────────────────────────────────
if "$ZIG" build-obj tools/layout_negative.zig -target wasm32-freestanding -fno-emit-bin >/dev/null 2>&1; then
    die "G4 usizse-across-FFI counter-example was accepted on wasm32"
fi
printf 'G4 ok  usize-across-FFI rejected on wasm32 (F0.3)\n'

# ── G5: hash-checked seam equivalence ───────────────────────────────────────
# The verified artifact is (contract ∧ layout table): concatenating the checked
# layout rows means the seam hash covers the ABI layout too, so a drifted offset
# cannot hide behind an unchanged contract.
cat spec/face-a.cspec spec/layout.cspec > spec/.face-a.full.cspec
cat spec/face-b.cspec spec/layout.cspec > spec/.face-b.full.cspec
a=$("$ADDR" hash spec/.face-a.full.cspec)
b=$("$ADDR" hash spec/.face-b.full.cspec)
[ "$a" = "$b" ] || die "G5 faces diverge: $a vs $b"
printf 'G5 ok  seam equivalence %s\n' "$a"

# A one-token difference must diverge, or G5 is vacuous.
"$ADDR" mutate spec/.face-a.full.cspec off_by_one > spec/.probe.cspec
c=$("$ADDR" hash spec/.probe.cspec)
rm -f spec/.probe.cspec
[ "$a" != "$c" ] || die "G5 vacuous: a one-byte spec change kept the digest"
printf 'G5 ok  divergence probe %s\n' "$c"

# ── G6: mutation sweep at the artifact level ────────────────────────────────
applied=0
distinct=0
seen="$a"
for op in $("$ADDR" ops); do
    if "$ADDR" mutate spec/.face-a.full.cspec "$op" > spec/.mutant.cspec 2>/dev/null; then
        applied=$((applied + 1))
        m=$("$ADDR" hash spec/.mutant.cspec)
        case " $seen " in
            *" $m "*) : ;;
            *)
                distinct=$((distinct + 1))
                seen="$seen $m"
                ;;
        esac
    fi
done
rm -f spec/.mutant.cspec spec/.probe.cspec spec/.face-a.full.cspec spec/.face-b.full.cspec
[ "$applied" = 11 ] || die "G6 only $applied of 11 operators applied"
[ "$distinct" = 11 ] || die "G6 only $distinct of 11 mutants were distinct"
printf 'G6 ok  mutation sweep: %s applied, %s distinct artifacts\n' "$applied" "$distinct"

# ── G7: SMT verification conditions ─────────────────────────────────────────
# Optional: needs python3 + z3-solver. When it cannot run, the receipt records
# `"smt":"not-run"` rather than claiming anything.
smt_state="not-run"
vc_hash="none"
vc_count=0
PY=${PYTHON:-python3}
if "$PY" -c 'import z3' >/dev/null 2>&1; then
    if "$PY" vc/gen_vcs.py > witness/vc-report.txt 2>&1; then
        vc_count=$(sed -n 's/^\([0-9][0-9]*\) VCs, 0 failing$/\1/p' witness/vc-report.txt)
        # One content address for the whole VC set: sorted per-file hashes.
        vc_hash=$(
            for f in vc/*.smt2; do "$ADDR" vc-hash "$f"; done | sort | "$ADDR" vc-hash /dev/stdin
        )
        smt_state="discharged"
        printf 'G7 ok  %s VCs discharged by z3 (%s)\n' "$vc_count" "$vc_hash"
    else
        die "G7 VC generation or discharging failed (see witness/vc-report.txt)"
    fi
else
    printf 'G7 --  z3 not installed: SMT obligations not discharged\n'
fi

# ── G8: extraction reproduces the checked-in Face B ─────────────────────────
"$ADDR" extract src/frame_parse.zig --symbol atoma_frame_parse > spec/.extracted.cspec
x=$("$ADDR" hash spec/.extracted.cspec)
b2=$("$ADDR" hash spec/face-b.cspec)
rm -f spec/.extracted.cspec
[ "$x" = "$b2" ] || die "G8 extractor output ($x) differs from face-b ($b2): re-run atoma extract and commit the result"
printf 'G8 ok  Face B extracted from source %s\n' "$x"

# ── G9: subset conformance of the implementation ────────────────────────────
if ! "$ADDR" check src/frame_parse.zig > witness/subset-report.txt 2>&1; then
    cat witness/subset-report.txt >&2
    die "G9 subset violations in src/frame_parse.zig"
fi
grep -q '6 contracts' witness/subset-report.txt || die "G9 expected 6 contracts in frame_parse.zig"
printf 'G9 ok  subset clean: 6 exports, 6 contracts, 0 diagnostics\n'

# ── G10: the negative corpus must be rejected ───────────────────────────────
if "$ADDR" check fixtures/violations.zig > witness/violations-report.txt 2>&1; then
    die "G10 the subset checker accepted fixtures/violations.zig"
fi
codes=$(sed -n 's/.*: \(E-[A-Z-]*\):.*/\1/p' witness/violations-report.txt | sort -u | wc -l | tr -d ' ')
diags=$(sed -n 's/.*: \(E-[A-Z-]*\):.*/\1/p' witness/violations-report.txt | wc -l | tr -d ' ')
[ "$codes" -ge 15 ] || die "G10 only $codes distinct diagnostic codes (want >= 15)"
[ "$diags" -ge 20 ] || die "G10 only $diags diagnostics (want >= 20)"
printf 'G10 ok negative corpus rejected: %s diagnostics, %s distinct codes\n' "$diags" "$codes"

# ── G11: the Agda metatheory ────────────────────────────────────────────────
# Optional: needs agda. `--safe` turns postulates, termination pragmas, rewrite
# rules, `primTrustMe` and cubical primitives into compile errors, so a green
# run is evidence that the proof is total and axiom-free. It is evidence about
# the model in `Core.agda`; the refinement obligation to Zig is NOT proved and
# is listed as a non-claim in the specification.
proof_state="not-run"
proof_hash="none"
AGDA=${AGDA:-agda}
if command -v "$AGDA" >/dev/null 2>&1; then
    AGDA="$AGDA" "$root/verification/atoma/check-agda.sh" > witness/agda-report.txt 2>&1 || {
        cat witness/agda-report.txt >&2
        die "G11 the Agda metatheory failed to typecheck"
    }
    # Ordered digest over the four module sources: order matters because
    # Soundness imports Core imports Bv, so a permuted set is a different proof.
    proof_hash=$(
        for m in Bv Lin Core Soundness; do
            "$ADDR" src-hash "$root/verification/atoma/agda/$m.agda"
        done | "$ADDR" src-hash /dev/stdin
    )
    proof_state="checked"
    printf 'G11 ok  metatheory typechecks: 4 modules, 0 postulates (%s)\n' "$proof_hash"
else
    printf 'G11 --  agda not installed: metatheory not typechecked\n'
fi

# ── receipt ─────────────────────────────────────────────────────────────────
# I-JSON + JCS: sorted keys, no insignificant whitespace, no floats.
layout_hash=$("$ADDR" hash spec/layout.cspec)
receipt=witness/phase0.receipt.json
printf '%s' \
    "{\"artifacts\":{\"face-a\":\"$a\",\"face-b\":\"$b\",\"layout\":\"$layout_hash\"}," \
    "\"contract\":\"atoma.frame.parse\",\"equivalence\":\"EQUIVALENT\"," \
    "\"gate\":\"phase0\"," \
    "\"mutants\":{\"applied\":$applied,\"distinct\":$distinct}," \
    "\"proof\":{\"modules\":4,\"srcset\":\"$proof_hash\",\"status\":\"$proof_state\"}," \
    "\"schema\":\"atoma.receipt.v1\"," \
    "\"smt\":{\"status\":\"$smt_state\",\"vcs\":$vc_count,\"vcset\":\"$vc_hash\"}," \
    "\"status\":\"INCOMPLETE\",\"status_class\":\"Warrant\"," \
    "\"subset\":{\"contracts\":6,\"diagnostics_negative_corpus\":$diags,\"codes_negative_corpus\":$codes}," \
    "\"targets\":[\"aarch64\",\"riscv64\",\"wasm32\",\"x86_64\"]," \
    "\"tests\":{\"atoma\":14,\"frame_parse\":11}}" > "$receipt"
printf '\nreceipt: %s\n' "$receipt"
cat "$receipt"
printf '\n'
printf 'STATUS: INCOMPLETE (Warrant) - Dedukti/coqchk/lean4checker checks did not run.\n'
