#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/scalar-proof-evidence/word"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 60 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
cp "$root/verification/atoma/consumer/agda/CanonicalWord"*.agda "$work/"
cp "$root/verification/atoma/consumer/lean4/CanonicalWord.lean" "$work/"
cp "$root/verification/atoma/consumer/coq/CanonicalWord.v" "$work/"
cd "$work"
# The strict compatible Agda proof is the first mandatory leg.
agda --safe --without-K --cubical-compatible --double-check --warning=error CanonicalWord.agda > "$out/agda.txt" 2>&1
failed=0
if ! lean CanonicalWord.lean > "$out/lean-assumptions.txt" 2>&1; then failed=1; fi
# Pinned Lean emits these exact reports. Reject custom axioms, duplicate or
# missing theorem reports, unexpected output and changes to approved axioms.
cat > "$work/expected-lean.txt" <<'REPORTS'
'CanonicalWord.decode_exact' depends on axioms: [propext, Quot.sound]
'CanonicalWord.noncanonical_refused' depends on axioms: [propext, Quot.sound]
'CanonicalWord.encode_injective' depends on axioms: [propext, Quot.sound]
'CanonicalWord.canonical_word_range' depends on axioms: [propext, Classical.choice, Quot.sound]
REPORTS
LC_ALL=C sort "$work/expected-lean.txt" > "$work/expected-lean-sorted.txt"
approved_lean_report() {
    LC_ALL=C sort "$1" > "$work/actual-lean-sorted.txt"
    cmp -s "$work/expected-lean-sorted.txt" "$work/actual-lean-sorted.txt"
}
if ! approved_lean_report "$out/lean-assumptions.txt"; then failed=1; fi
# Compile a real counterfeit proof: it has no sorryAx and still reports all
# four theorem names, but replaces the payload lemma with a custom axiom.
awk '
  /^theorem payload_encode / {
    print "axiom forged : False"
    print "theorem payload_encode (b : Nat) : payload (encode b) = b := False.elim forged"
    skip=1; next
  }
  /^theorem decode_exact / { skip=0 }
  !skip { print }
' CanonicalWord.lean > Forged.lean
if ! lean Forged.lean > "$out/lean-custom-axiom.txt" 2>&1; then failed=1; fi
if ! grep -q 'CanonicalWord.forged' "$out/lean-custom-axiom.txt"; then failed=1; fi
if approved_lean_report "$out/lean-custom-axiom.txt"; then failed=1; fi
head -n 3 "$out/lean-assumptions.txt" > "$out/lean-missing-report.txt"
if approved_lean_report "$out/lean-missing-report.txt"; then failed=1; fi
cat "$out/lean-assumptions.txt" "$out/lean-assumptions.txt" > "$out/lean-duplicate-reports.txt"
if approved_lean_report "$out/lean-duplicate-reports.txt"; then failed=1; fi
if ! coqc -q CanonicalWord.v > "$out/coq-assumptions.txt" 2>&1; then failed=1; fi
if [[ $(grep -c '^Closed under the global context$' "$out/coq-assumptions.txt") != 4 ]]; then failed=1; fi
if ! coqchk -silent -Q . '' CanonicalWord > "$out/coqchk.txt" 2>&1; then failed=1; fi
if ! agda --safe --cubical --double-check --warning=error CanonicalWordCubical.agda > "$out/cubical.txt" 2>&1; then failed=1; fi
sha256sum ./*.agda ./*.lean ./*.v > "$out/inputs.sha256"
[[ $failed == 0 ]]
echo 'WORD THEORY PASS: universal canonical decoder models; source and cross-model correspondence remain separate'
