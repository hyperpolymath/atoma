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
if grep -q 'sorryAx' "$out/lean-assumptions.txt"; then failed=1; fi
if [[ $(grep -c '^.CanonicalWord\.' "$out/lean-assumptions.txt") != 4 ]]; then failed=1; fi
if ! coqc -q CanonicalWord.v > "$out/coq-assumptions.txt" 2>&1; then failed=1; fi
if [[ $(grep -c '^Closed under the global context$' "$out/coq-assumptions.txt") != 4 ]]; then failed=1; fi
if ! coqchk -silent -Q . '' CanonicalWord > "$out/coqchk.txt" 2>&1; then failed=1; fi
if ! agda --safe --cubical --double-check --warning=error CanonicalWordCubical.agda > "$out/cubical.txt" 2>&1; then failed=1; fi
sha256sum ./*.agda ./*.lean ./*.v > "$out/inputs.sha256"
[[ $failed == 0 ]]
echo 'WORD THEORY PASS: universal canonical decoder models; source and cross-model correspondence remain separate'
