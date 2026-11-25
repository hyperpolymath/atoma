#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/scalar-proof-evidence/wrapper-theory"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 50 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
cp "$root/verification/atoma/consumer/agda/WrapperEffects"*.agda "$work/"
cp "$root/verification/atoma/consumer/lean4/WrapperEffects.lean" "$work/"
cd "$work"
agda --safe --without-K --cubical-compatible --double-check --warning=error WrapperEffects.agda > "$out/agda.txt" 2>&1
lean WrapperEffects.lean > "$out/lean.txt" 2>&1
awk '
BEGIN {names["normalReturnFrame"]=1; names["invalidSpanCleanup"]=1; names["aliasCounterexample"]=1; names["aliasBreaksFrame"]=1; names["scanRefinesFold"]=1}
{
  found=0
  for (n in names) {
    expected="\047WrapperEffects." n "\047 does not depend on any axioms"
    if ($0 == expected && names[n] == 1) {names[n]=2; found=1; count++}
  }
  if (!found) exit 1
}
END {if (count != 5) exit 1}' "$out/lean.txt"
agda --safe --cubical --double-check --warning=error WrapperEffectsCubical.agda > "$out/cubical.txt" 2>&1
sed -e 's/module WrapperEffects where/module WrapperEffectsMutant where/' \
  -e 's/finish s = registry (rest s) (mcp s) false/finish s = registry (rest s) (mcp s) true/' WrapperEffects.agda > WrapperEffectsMutant.agda
if agda --safe --cubical-compatible --double-check --warning=error WrapperEffectsMutant.agda > "$out/reject-cleanup.txt" 2>&1; then exit 1; fi
grep -q '!=' "$out/reject-cleanup.txt"
sha256sum ./*.agda ./*.lean > "$out/inputs.sha256"
echo 'WRAPPER THEORY PASS: compatible Agda, audited Lean, Cubical and rejecting cleanup control'
