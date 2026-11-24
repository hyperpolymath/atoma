#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Proof development and adversarial controls; consumer CI adds Idris authority.
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
for tool in zig agda lean coqc coqchk; do command -v "$tool" >/dev/null; done
[[ $(zig version) == 0.15.2 ]]
[[ $(lean --version) == 'Lean (version 4.15.0,'* ]]
out="$root/build/scalar-proof-evidence"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 50 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
cp verification/atoma/consumer/agda/ScalarReflection.agda "$work/"
cp verification/atoma/consumer/agda/ScalarReflectionCubical.agda "$work/"
cp verification/atoma/consumer/lean4/ScalarReflection.lean "$work/"
cp verification/atoma/consumer/coq/ScalarSource.v "$work/"
(
    cd "$work"
    agda --safe --without-K --cubical-compatible --double-check --warning=error ScalarReflection.agda
    # Collect each independent leg's diagnostics, but every leg is mandatory.
    theory_failed=0
    if ! lean ScalarReflection.lean > "$out/lean-assumptions.txt" 2>&1; then theory_failed=1; fi
    if [[ $(grep -c 'does not depend on any axioms' "$out/lean-assumptions.txt") != 2 ]]; then theory_failed=1; fi
    if ! coqc -q ScalarSource.v > "$out/coq-assumptions.txt" 2>&1; then theory_failed=1; fi
    if [[ $(grep -c '^Closed under the global context$' "$out/coq-assumptions.txt") != 2 ]]; then theory_failed=1; fi
    if ! coqchk -silent -Q . '' ScalarSource > "$out/coqchk.txt" 2>&1; then theory_failed=1; fi
    if ! agda --safe --cubical --double-check --warning=error ScalarReflectionCubical.agda > "$out/cubical.txt" 2>&1; then theory_failed=1; fi
    [[ $theory_failed == 0 ]]
) > "$out/theory.txt" 2>&1
(cd tools/atoma && zig build test && zig build)
atoma="$root/tools/atoma/zig-out/bin/atoma"
# These fixture tables are test data only. Real consumer receipts require fresh
# tables from the pinned Idris ABI modules; never promote these fixtures.
awk 'BEGIN {for(i=0;i<256;i++) printf "%d %.0f\n",i,i*4294967296+1}' > "$work/encode.tsv"
awk 'BEGIN {for(i=0;i<256;i++) print i,(i>=1 && i<=9 ? 1 : 0)}' > "$work/known.tsv"
for fixture in encode known; do
    "$atoma" scalar-coq "tests/consumer-scalar/$fixture.zig" "$work/$fixture.tsv" > "$work/AtomaProof.v"
    bash scripts/atoma-scalar-capsule.sh "tests/consumer-scalar/$fixture.zig" "$work/$fixture.tsv" "$work/AtomaProof.v"
    (cd "$work" && coqc -q AtomaProof.v && coqchk -silent -Q . '' AtomaProof) > "$out/$fixture.txt" 2>&1
    "$atoma" scalar-coq-audit "tests/consumer-scalar/$fixture.zig" "$work/$fixture.tsv" > "$work/Audit.v"
    (cd "$work" && coqc -q Audit.v) > "$out/$fixture-audit.txt" 2>&1
    [[ $(grep -c '^Closed under the global context$' "$out/$fixture-audit.txt") == 2 ]]
done
reject_proof() {
    local name=$1 source=$2 table=$3
    "$atoma" scalar-coq "$source" "$table" > "$work/Bad.v"
    if (cd "$work" && coqc -q Bad.v) > "$out/$name.txt" 2>&1; then
        echo "FAIL accepted $name" >&2; exit 1
    fi
    grep -q 'Unable to unify' "$out/$name.txt"
}
sed 's/<< 32/<< 31/' tests/consumer-scalar/encode.zig > "$work/shift.zig"
reject_proof wrong-shift "$work/shift.zig" "$work/encode.tsv"
sed 's/| 1/| 0/' tests/consumer-scalar/encode.zig > "$work/tag.zig"
reject_proof wrong-tag "$work/tag.zig" "$work/encode.tsv"
sed 's/<= 9/<= 10/' tests/consumer-scalar/known.zig > "$work/range.zig"
reject_proof wrong-range "$work/range.zig" "$work/known.tsv"
cat tests/consumer-scalar/known.zig > "$work/import.zig"
printf '\nconst hidden = @import("hidden.zig");\n' >> "$work/import.zig"
reject_proof unsupported-import "$work/import.zig" "$work/known.tsv"
cp "$work/known.tsv" "$work/wrong-contract.tsv"
sed -i 's/^9 1$/9 0/' "$work/wrong-contract.tsv"
reject_proof wrong-contract tests/consumer-scalar/known.zig "$work/wrong-contract.tsv"
"$atoma" scalar-coq tests/consumer-scalar/known.zig "$work/known.tsv" > "$work/stale.v"
if bash scripts/atoma-scalar-capsule.sh "$work/range.zig" "$work/known.tsv" "$work/stale.v" > "$out/stale-source.txt" 2>&1; then
    echo 'FAIL accepted stale source capsule' >&2; exit 1
fi
grep -q 'capsule differs' "$out/stale-source.txt"
sha256sum verification/atoma/consumer/{coq,agda,lean4}/* tools/atoma/src/scalar.zig > "$out/inputs.sha256"
echo 'SCALAR THEORY PASS: finite reflection and raw-source fixtures; consumer and compiler boundaries remain separate'
