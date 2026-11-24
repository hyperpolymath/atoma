#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
[[ $# == 3 ]] || exit 2
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
source_path=$(realpath "$1")
table_path=$(realpath "$2")
out=$(realpath -m "$3")
mkdir "$out"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export REAL_COQC
REAL_COQC=$(command -v coqc)
mkdir "$work/bin"
cat > "$work/bin/echidna" <<'FAKE'
#!/usr/bin/env bash
set -euo pipefail
[[ $1 == prove ]]
goal=$2
case "$FAKE_MODE" in
    verdict-only) ;;
    wrong-theorem)
        cat > "$goal" <<'COQ'
Theorem atoma_scalar : True. Proof. exact I. Qed.
Theorem atoma_scalar_range : True. Proof. exact I. Qed.
COQ
        "$REAL_COQC" -q "$goal" >&2 ;;
    admitted)
        sed -i '/^Proof\. exact (ScalarSource\.check_/c\Admitted.' "$goal"
        "$REAL_COQC" -q "$goal" >&2 ;;
    changed-checker)
        "$REAL_COQC" -q "$goal" >&2
        printf 'tamper' >> ScalarSource.vo ;;
    changed-capsule)
        # Whitespace preserves interpreted behavior, but cannot preserve identity.
        sed -i '/^Definition source_bytes :/s/\]\.$/; 10]./' "$goal"
        "$REAL_COQC" -q "$goal" >&2 ;;
    *) exit 2 ;;
esac
jq -cn --arg goal "$goal" '{schema:"echidna.prove.result/1",status:"verified",prover:"Coq",goal:$goal,trust:{axioms:[],confidence:null}}'
FAKE
chmod +x "$work/bin/echidna"
for mode in verdict-only wrong-theorem admitted changed-checker changed-capsule; do
    if PATH="$work/bin:$PATH" FAKE_MODE="$mode" bash "$root/scripts/atoma-scalar-replay.sh" \
        "$source_path" "$table_path" "$out/$mode" > "$out/$mode.txt" 2>&1; then
        echo "FAIL scalar replay accepted $mode" >&2; exit 1
    fi
    case "$mode" in
        verdict-only) grep -q 'missing compiled proof' "$out/$mode.txt" ;;
        wrong-theorem) grep -q 'expected to have type' "$out/$mode/assumptions.txt" ;;
        admitted) grep -q 'unexpected assumption closure' "$out/$mode.txt" ;;
        changed-checker) grep -q 'backend changed the independently compiled source checker' "$out/$mode.txt" ;;
        changed-capsule) grep -q 'capsule differs' "$out/$mode.txt" ;;
    esac
done
echo 'SCALAR REPLAY CONTROLS PASS: verdict, theorem, assumptions, checker and capsule attacks refused'
