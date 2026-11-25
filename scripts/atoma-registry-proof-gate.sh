#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/scalar-proof-evidence/registry-theory"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 50 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
cp "$root/verification/atoma/consumer/agda/RegistryState"*.agda "$work/"
cp "$root/verification/atoma/consumer/lean4/RegistryState.lean" "$work/"
cd "$work"
agda --safe --without-K --cubical-compatible --double-check --warning=error RegistryState.agda > "$out/agda.txt" 2>&1
lean RegistryState.lean > "$out/lean.txt" 2>&1
# Exactly these six declarations, with no axioms (including no sorryAx).
awk '
BEGIN {names["updateFrame"]=1; names["updateIdentity"]=1; names["beginIdentity"]=1;
       names["reentrantRefused"]=1; names["normalReturnFrame"]=1; names["normalReturnIdle"]=1}
{
  found=0
  for (n in names) {
    expected = "\047RegistryState." n "\047 does not depend on any axioms"
    if ($0 == expected && names[n] == 1) {names[n]=2; found=1; count++}
  }
  if (!found) exit 1
}
END {if (count != 6) exit 1}' "$out/lean.txt"
agda --safe --cubical --double-check --warning=error RegistryStateCubical.agda > "$out/cubical.txt" 2>&1
sed -e 's/module RegistryState where/module RegistryStateMutant where/' \
    -e 's/state e (mcp s) (active s)/state e e (active s)/' RegistryState.agda > RegistryStateMutant.agda
if agda --safe --cubical-compatible --double-check --warning=error RegistryStateMutant.agda > "$out/reject-frame.txt" 2>&1; then exit 1; fi
grep -q '!=' "$out/reject-frame.txt"
sha256sum ./*.agda ./*.lean > "$out/inputs.sha256"
echo 'REGISTRY THEORY PASS: compatible Agda, independent axiom-free Lean witnesses, full Cubical paths'

