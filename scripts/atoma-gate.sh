#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# The Atoma CI entrypoint: all checks required; no missing-tool success path.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
export ZIG=${ZIG:-zig} Z3=${Z3:-z3} AGDA=${AGDA:-agda} IDRIS2=${IDRIS2:-idris2}
for tool in "$ZIG" "$Z3" "$AGDA" "$IDRIS2"; do
    command -v "$tool" >/dev/null || { echo "FAIL missing required tool: $tool" >&2; exit 1; }
done
[[ $("$ZIG" version) == 0.15.2 ]] || { echo 'FAIL expected Zig 0.15.2'; exit 1; }
[[ $("$Z3" --version) == 'Z3 version 4.13.3 '* ]] || { echo 'FAIL expected Z3 4.13.3'; exit 1; }
case $("$AGDA" --version) in
    'Agda version 2.6.3'|'Agda version 2.6.4.3') ;;
    *) echo 'FAIL unsupported Agda version'; exit 1 ;;
esac
[[ $("$IDRIS2" --version) == 'Idris 2, version 0.8.0'* ]] || { echo 'FAIL expected Idris2 0.8.0'; exit 1; }
evidence="$root/build/atoma-evidence"
mkdir -p "$evidence"
{
    "$ZIG" version; "$Z3" --version; "$AGDA" --version; "$IDRIS2" --version
    for tool in "$ZIG" "$Z3" "$AGDA" "$IDRIS2"; do
        sha256sum "$(command -v "$tool")"
    done
    git rev-parse HEAD
    git status --porcelain
} > "$evidence/environment.txt"

# Coverage is checked against the owned proof directories, not the inherited
# template directory alone. Unregistered and stale entries both fail.
for prover in agda idris2; do
    case "$prover" in
        agda) dir=verification/atoma/agda; ext=agda ;;
        idris2) dir=examples/atoma/frame-v1/abi; ext=idr ;;
        *) echo "FAIL unregistered prover: $prover" >&2; exit 1 ;;
    esac
    awk -F '|' -v dir="$dir" '$1 == dir { if ($3 != "gated") exit 1; print $1 "/" $2 }' \
        "verification/proofs/$prover/MANIFEST" | sort > "$evidence/$prover-listed.txt"
    find "$dir" -name "*.$ext" -not -path '*/build/*' | sort > "$evidence/$prover-found.txt"
    diff -u "$evidence/$prover-listed.txt" "$evidence/$prover-found.txt"
done
bash examples/atoma/frame-v1/verify.sh | tee "$evidence/phase0.log"
(cd tools/atoma && "$ZIG" build test)

atoma="$root/tools/atoma/zig-out/bin/atoma"
pilot=examples/atoma/source-u8
"$atoma" source-check "$pilot/increment.zig" | tee "$evidence/source-check.txt"
"$atoma" source-vc "$pilot/increment.zig" > "$evidence/source-good.smt2"
good_verdict=$("$Z3" -T:15 -smt2 "$evidence/source-good.smt2")
[[ "$good_verdict" == unsat ]]
"$atoma" source-vc "$pilot/wrong-body.zig" > "$evidence/source-bad.smt2"
bad_verdict=$("$Z3" -T:15 -smt2 "$evidence/source-bad.smt2")
[[ "$bad_verdict" == sat ]]
printf 'good-body %s\nwrong-body %s\n' "$good_verdict" "$bad_verdict" > "$evidence/source-verdicts.txt"
if "$atoma" source-check "$pilot/wrong-body.zig" > "$evidence/source-counterexample.txt"; then
    echo 'FAIL accepted wrong body with unchanged contract'; exit 1
fi
grep -q '^SOURCE-COUNTEREXAMPLE ' "$evidence/source-counterexample.txt"
if "$atoma" source-check "$pilot/recursive.zig" > "$evidence/source-recursion.txt"; then
    echo 'FAIL accepted recursion in the source pilot'; exit 1
fi
grep -q '^SOURCE-REFUSED .*UnsupportedSource' "$evidence/source-recursion.txt"

# Compile and execute the real fixture over the entire input domain. The
# mutated executable must fail the same witness; SMT alone is not this check.
"$ZIG" build-obj "$pilot/increment.zig" -femit-bin="$evidence/increment.o"
"$ZIG" test "$pilot/compiled-witness.zig" "$evidence/increment.o" 2>&1 | tee "$evidence/compiled-good.txt"
"$ZIG" build-obj "$pilot/wrong-body.zig" -femit-bin="$evidence/wrong-body.o"
if "$ZIG" test "$pilot/compiled-witness.zig" "$evidence/wrong-body.o" > "$evidence/compiled-bad.txt" 2>&1; then
    echo 'FAIL wrong executable survived exhaustive witness'; exit 1
fi
grep -q 'TestExpectedEqual' "$evidence/compiled-bad.txt"

bash scripts/atoma-gate-falsifiers.sh | tee "$evidence/falsifiers.txt"
# Bind the source, contracts, proof sources and gate definitions to this run.
# Exclude generated caches/witnesses to avoid self-referential digests.
find tools/atoma/src examples/atoma/frame-v1/src examples/atoma/frame-v1/abi \
    examples/atoma/frame-v1/spec examples/atoma/source-u8 verification/atoma \
    -type f \( -name '*.zig' -o -name '*.idr' -o -name '*.ipkg' -o -name '*.cspec' -o -name '*.agda' -o -name '*.sh' \) \
    -not -path '*/build/*' -print | LC_ALL=C sort | xargs sha256sum > "$evidence/inputs.sha256"
sha256sum tools/atoma/build.zig scripts/atoma-*.sh examples/atoma/frame-v1/verify.sh \
    verification/proofs/{agda,idris2}/MANIFEST .github/workflows/atoma.yml >> "$evidence/inputs.sha256"
cp examples/atoma/frame-v1/witness/phase0.receipt.json "$evidence/"
echo 'ATOMA GATE PASS — INCOMPLETE (Warrant); no program-refinement or kernel-replay claim'
