#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Replay the closed u8 model. Never issues a COMPLETE receipt.
set -euo pipefail
[[ $# == 3 ]] || { echo 'usage: atoma-replay.sh SOURCE PROOF NEW_EVIDENCE_DIRECTORY' >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && pwd)
export ATOMA=${ATOMA:-$root/tools/atoma/zig-out/bin/atoma}
export ECHIDNA=${ECHIDNA:-echidna} COQC=${COQC:-coqc} COQCHK=${COQCHK:-coqchk}
fail() { echo "REPLAY-REFUSED: $*" >&2; exit 1; }
for tool in "$ATOMA" "$ECHIDNA" "$COQC" "$COQCHK" jq timeout sha256sum; do
    command -v "$tool" >/dev/null || fail "missing tool: $tool"
done
ATOMA=$(realpath "$(command -v "$ATOMA")")
ECHIDNA=$(realpath "$(command -v "$ECHIDNA")")
COQC=$(realpath "$(command -v "$COQC")")
COQCHK=$(realpath "$(command -v "$COQCHK")")
# The pinned ECHIDNA Coq backend invokes coqc by name. Audit that exact
# compiler, even when a caller supplies COQC as an absolute path.
[[ $(realpath "$(command -v coqc)") == $(realpath "$(command -v "$COQC")") ]] \
    || fail 'COQC differs from the compiler ECHIDNA will invoke'
source_path=$(realpath "$1")
proof_path=$(realpath "$2")
out=$(realpath -m "$3")
# No pre-existing .vo, receipt, or cached result may contribute to this run.
mkdir "$out" || fail 'evidence directory must be new'
cp "$source_path" "$out/source.zig"
cp "$proof_path" "$out/AtomaProof.v"
"$ATOMA" source-coq "$out/source.zig" > "$out/regenerated.v"
cmp -s "$out/AtomaProof.v" "$out/regenerated.v" || fail 'proof does not match current source and emitter'
cd "$out"
"$COQC" --version > coqc-version.txt
"$COQCHK" --version > coqchk-version.txt
"$ECHIDNA" --version > echidna-version.txt
case $(head -n 1 coqc-version.txt) in
    'The Coq Proof Assistant, version 8.18.0'|'The Rocq Prover, version 9.2') ;;
    *) fail 'unsupported Coq/Rocq profile' ;;
esac
# ECHIDNA's backend compiles this exact source file. Its JSON verdict alone
# does not certify a proof or the absence of assumptions.
timeout -k 5 120 "$ECHIDNA" prove "$out/AtomaProof.v" --prover coq --timeout 90 --output json \
    > echidna.json 2> echidna.stderr || fail 'ECHIDNA did not verify the obligation'
jq -e -s --arg goal "$out/AtomaProof.v" '
    length == 1 and (.[0] | .schema == "echidna.prove.result/1" and
    .status == "verified" and .prover == "Coq" and .goal == $goal and
    .trust.axioms == [] and .trust.confidence == null)' echidna.json >/dev/null \
    || fail 'malformed, non-verified or assumption-bearing ECHIDNA result'
[[ -s AtomaProof.vo ]] || fail 'ECHIDNA produced no compiled proof'
# Check the actual compiled library, recursively, with no -admit/-norec.
timeout -k 5 120 "$COQCHK" -silent -Q . '' AtomaProof > coqchk.txt 2>&1 \
    || fail 'independent compiled-proof check failed'
# Restate the expected theorem from the source snapshot, never by trusting
# body/specification definitions in the returned .vo. A valid proof of a
# different model must fail even if the backend leaves the expected .v intact.
# coqchk also permits axioms, so audit this theorem's full assumption closure.
"$ATOMA" source-coq-audit source.zig > Audit.v
timeout -k 5 120 "$COQC" -q -Q . '' Audit.v > assumptions.txt 2> assumptions.stderr \
    || fail 'theorem type or assumption audit failed'
[[ $(grep -c '^Closed under the global context$' assumptions.txt) == 1 ]] \
    || fail 'the theorem is not closed under the global context'
! grep -q '^Axioms:' assumptions.txt || fail 'axioms in theorem closure'
cmp -s "$source_path" source.zig || fail 'source changed during replay'
cmp -s "$proof_path" AtomaProof.v || fail 'proof changed during replay'
cmp -s AtomaProof.v regenerated.v || fail 'proof was changed by a subprocess'
sha256sum source.zig AtomaProof.v AtomaProof.vo Audit.v Audit.vo echidna.json \
    coqchk.txt assumptions.txt coqc-version.txt coqchk-version.txt echidna-version.txt > inputs.sha256
for tool in "$ATOMA" "$ECHIDNA" "$COQC" "$COQCHK"; do
    sha256sum "$(command -v "$tool")"
done > tools.sha256
source_digest=$(sha256sum source.zig | cut -d ' ' -f 1)
proof_digest=$(sha256sum AtomaProof.v | cut -d ' ' -f 1)
jq -cnS --arg source "$source_digest" --arg proof "$proof_digest" \
    '{schema:"atoma.replay.u8/1",status:"INCOMPLETE",scope:"source-derived finite u8 model",
      source_sha256:$source,proof_sha256:$proof,echidna:"verified",coqchk:"checked",
      assumptions:[],refinement:"unproved"}' > receipt.json.tmp
mv receipt.json.tmp receipt.json
echo 'REPLAY-MODEL-CHECKED: ECHIDNA + coqchk; INCOMPLETE, Zig refinement unproved'
