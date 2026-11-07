#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
export ATOMA=${ATOMA:-$root/tools/atoma/zig-out/bin/atoma}
export ECHIDNA=${ECHIDNA:-echidna} COQC=${COQC:-coqc} COQCHK=${COQCHK:-coqchk}
work=$(mktemp -d "$root/build/atoma-evidence/replay.XXXXXX")
pilot="$root/examples/atoma/source-u8"
replay="$root/scripts/atoma-replay.sh"
"$ATOMA" source-coq "$pilot/increment.zig" > "$work/good.v"
bash "$replay" "$pilot/increment.zig" "$work/good.v" "$work/good"
(cd "$work/good" && sha256sum -c inputs.sha256)
printf '/// @ensures result == x +%% 0\nexport fn identity(x: u8) callconv(.c) u8 { return x; }\n' > "$work/identity.zig"
"$ATOMA" source-coq "$work/identity.zig" > "$work/identity.v"
bash "$replay" "$work/identity.zig" "$work/identity.v" "$work/identity"
reject() {
    local name=$1 expected=$2; shift 2
    if "$@" > "$work/$name.log" 2>&1; then
        echo "FAIL replay accepted $name" >&2; exit 1
    fi
    grep -qF "$expected" "$work/$name.log" || { cat "$work/$name.log" >&2; exit 1; }
    [[ ! -e "$work/$name/receipt.json" ]] || { echo 'FAIL failure published a receipt' >&2; exit 1; }
    echo "REPLAY-FALSIFIER-KILLED $name"
}
"$ATOMA" source-coq "$pilot/wrong-body.zig" > "$work/wrong.v"
reject wrong-body 'ECHIDNA did not verify' bash "$replay" "$pilot/wrong-body.zig" "$work/wrong.v" "$work/wrong-body"
printf '/// @ensures result == x +%% 0\nexport fn constant(x: u8) callconv(.c) u8 { return 0; }\n' > "$work/literal.zig"
"$ATOMA" source-coq "$work/literal.zig" > "$work/literal.v"
reject literal 'ECHIDNA did not verify' bash "$replay" "$work/literal.zig" "$work/literal.v" "$work/literal"
cp "$pilot/increment.zig" "$work/changed.zig"
printf '\n// a source identity change\n' >> "$work/changed.zig"
reject stale-source 'proof does not match current source' bash "$replay" "$work/changed.zig" "$work/good.v" "$work/stale-source"
sed 's/Proof\. vm_compute\. reflexivity\. Qed\./Admitted./' "$work/good.v" > "$work/admitted.v"
reject admitted 'proof does not match current source' bash "$replay" "$pilot/increment.zig" "$work/admitted.v" "$work/admitted"
reject missing-kernel 'missing tool:' env COQCHK="$work/no-such-checker" bash "$replay" "$pilot/increment.zig" "$work/good.v" "$work/missing-kernel"
reject reused-directory 'evidence directory must be new' bash "$replay" "$pilot/increment.zig" "$work/good.v" "$work/good"
cat > "$work/fake-echidna" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ $1 == --version ]]; then echo 'echidna fake-negative-control'; exit 0; fi
case ${FAKE_MODE:?} in
    malformed) echo '{' ;;
    unknown) jq -cn --arg goal "$2" '{schema:"echidna.prove.result/1",status:"unknown",prover:"Coq",goal:$goal,trust:{axioms:[],confidence:null}}' ;;
    no-proof) jq -cn --arg goal "$2" '{schema:"echidna.prove.result/1",status:"verified",prover:"Coq",goal:$goal,trust:{axioms:[],confidence:null}}' ;;
    corrupt)
        "$REAL_ECHIDNA" "$@"
        printf 'corrupted compiled proof\n' > "${2%.v}.vo"
        ;;
    *) exit 2 ;;
esac
SH
chmod +x "$work/fake-echidna"
for mode in malformed unknown no-proof corrupt; do
    case $mode in
        malformed|unknown) reason='malformed, non-verified or assumption-bearing' ;;
        no-proof) reason='produced no compiled proof' ;;
        corrupt) reason='independent compiled-proof check failed' ;;
        *) exit 2 ;;
    esac
    reject "$mode" "$reason" env REAL_ECHIDNA="$ECHIDNA" ECHIDNA="$work/fake-echidna" FAKE_MODE="$mode" \
        bash "$replay" "$pilot/increment.zig" "$work/good.v" "$work/$mode"
done
# This control demonstrates why coqchk alone cannot discharge the no-axioms
# obligation: an admitted theorem compiles and checks, but is not closed.
mkdir "$work/axiom-control"
printf 'Theorem admitted_control : False. Admitted.\nPrint Assumptions admitted_control.\n' > "$work/axiom-control/Control.v"
(
    cd "$work/axiom-control"
    timeout -k 5 120 "$COQC" -q Control.v > assumptions.txt 2> assumptions.stderr
    timeout -k 5 120 "$COQCHK" -silent -Q . '' Control > coqchk.txt 2>&1
    grep -q '^Axioms:' assumptions.txt
    ! grep -q '^Closed under the global context$' assumptions.txt
)
echo 'REPLAY GATE PASS: two source-derived models checked, 10 rejection controls, axiom control; INCOMPLETE'
