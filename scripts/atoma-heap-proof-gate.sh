#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
parent="$root/build/scalar-proof-evidence/heap"
mkdir -p "$parent"
out=$(mktemp -d "$parent/run.XXXXXXXX")
work=$(mktemp -d)
echo INCOMPLETE > "$out/result.txt"
trap 'status=$?; if ((status)); then echo FAIL > "$out/result.txt"; tail -n 45 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
sources=(verification/atoma/consumer/agda/HeapOwnership.agda
  verification/atoma/consumer/agda/HeapOwnershipCubical.agda
  verification/atoma/consumer/lean4/HeapOwnership.lean
  verification/atoma/consumer/coq/HeapOwnership.v scripts/atoma-heap-proof-gate.sh)
(cd "$root"; sha256sum "${sources[@]}") > "$out/source-inputs.sha256"
for source in "${sources[@]:0:4}"; do cp "$root/$source" "$work/"; cmp "$root/$source" "$work/$(basename "$source")"; done
(cd "$root"; sha256sum -c "$out/source-inputs.sha256") > "$out/snapshot-recheck.txt"
cd "$work"
# Check the staged copies against the ORIGINAL digests, not a fresh hash of
# whatever was staged: a transient edit restored before the recheck must fail.
while read -r digest path; do
  [[ $path == scripts/* ]] || printf '%s  %s\n' "$digest" "${path##*/}"
done < "$out/source-inputs.sha256" > "$out/checked-inputs.sha256"
sha256sum -c "$out/checked-inputs.sha256" > "$out/staged-recheck.txt"
agda --safe --without-K --cubical-compatible --double-check --warning=error HeapOwnership.agda > "$out/agda.txt" 2>&1
lean HeapOwnership.lean > "$out/lean.txt" 2>&1
awk '
BEGIN {
  split("releaseBorrowedRefused releaseRetainedRefused writeBorrowedRefused failedPreserves borrowReturnCell borrowPreservesBytes releaseRemovesOwned releaseFramesOther acquireLiveRefused spanLength", required, " ")
  for (i in required) names[required[i]]=1
}
{
  found=0
  for (n in names) {
    expected="\047HeapOwnership." n "\047 does not depend on any axioms"
    if ($0 == expected && names[n] == 1) {names[n]=2; found=1; count++}
  }
  if (!found) exit 1
}
END {if (count != 10) exit 1}' "$out/lean.txt"
coqc -q HeapOwnership.v > "$out/coq.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/coq.txt") == 10 ]]
# A zero-exit build may still print warnings; accept only the ten audit lines.
if grep -qv '^Closed under the global context$' "$out/coq.txt"; then echo 'FAIL: Coq diagnostics' >&2; exit 1; fi
if grep -q '^Axioms:' "$out/coq.txt"; then echo 'FAIL: heap proof axioms' >&2; exit 1; fi
coqchk -silent -Q . '' HeapOwnership > "$out/coqchk.txt" 2>&1
agda --safe --cubical --double-check --warning=error HeapOwnershipCubical.agda > "$out/cubical.txt" 2>&1

# These mutate the actual operational definitions; unrelated compiler failures
# are not accepted as evidence that the intended mathematical obligation failed.
sed -e 's/module HeapOwnership where/module HeapOwnershipMutant where/' \
  -e 's/cell-step release (live bytes retained (suc readers)) = nothing/cell-step release (live bytes retained (suc readers)) = just vacant/' \
  HeapOwnership.agda > HeapOwnershipMutant.agda
if agda --safe --without-K --cubical-compatible --double-check --warning=error HeapOwnershipMutant.agda > "$out/reject-borrowed-release.txt" 2>&1; then
  echo 'FAIL: freeing borrowed region accepted' >&2; exit 1
fi
grep -q '!=' "$out/reject-borrowed-release.txt"
sed -e 's/module HeapOwnership where/module HeapOwnershipCorrupt where/' \
  -e 's/cell-step borrow-read (live bytes retained readers) = just (live bytes retained (suc readers))/cell-step borrow-read (live bytes retained readers) = just (live (zero ∷ bytes) retained (suc readers))/' \
  HeapOwnership.agda > HeapOwnershipCorrupt.agda
if agda --safe --without-K --cubical-compatible --double-check --warning=error HeapOwnershipCorrupt.agda > "$out/reject-borrow-corruption.txt" 2>&1; then
  echo 'FAIL: borrow byte corruption accepted' >&2; exit 1
fi
grep -q '!=' "$out/reject-borrow-corruption.txt"
sed 's/| Release, Live _ 0 0 => Some Vacant/| Release, Live _ 0 _ => Some Vacant/' HeapOwnership.v > HeapOwnershipBad.v
if coqc -q HeapOwnershipBad.v > "$out/reject-coq-release.txt" 2>&1; then
  echo 'FAIL: Coq borrowed release mutation accepted' >&2; exit 1
fi
grep -q 'Unable to unify' "$out/reject-coq-release.txt"
sha256sum -c "$out/checked-inputs.sha256" > "$out/checked-input-recheck.txt"
(cd "$root"; sha256sum -c "$out/source-inputs.sha256") > "$out/source-recheck.txt"
cp HeapOwnership.agda HeapOwnershipCubical.agda HeapOwnership.lean HeapOwnership.v HeapOwnership.vo "$out/"
{ agda --version; lean --version; coqc --version; } > "$out/versions.txt"
for tool in agda lean coqc coqchk; do sha256sum "$(command -v "$tool")"; done > "$out/tools.sha256"
echo PASS > "$out/result.txt"
echo 'HEAP THEORY PASS: region updates, borrow/release and span laws; native pointer and authority correspondence remain premises'
