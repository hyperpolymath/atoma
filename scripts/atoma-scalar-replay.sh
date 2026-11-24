#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
[[ $# == 3 ]] || { echo 'usage: atoma-scalar-replay.sh SOURCE TABLE NEW_EVIDENCE_DIRECTORY' >&2; exit 2; }
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
ATOMA=${ATOMA:-$root/tools/atoma/zig-out/bin/atoma}
fail() { echo "SCALAR-REPLAY-REFUSED: $*" >&2; exit 1; }
for tool in "$ATOMA" echidna coqc coqchk jq timeout sha256sum; do
    command -v "$tool" >/dev/null || fail "missing tool: $tool"
done
ATOMA=$(realpath "$(command -v "$ATOMA")")
source_path=$(realpath "$1")
table_path=$(realpath "$2")
out=$(realpath -m "$3")
mkdir "$out" || fail 'evidence directory must be new'
cp "$source_path" "$out/source.zig"
cp "$table_path" "$out/contract.tsv"
cp "$root/verification/atoma/consumer/coq/ScalarSource.v" "$out/"
"$ATOMA" scalar-coq "$out/source.zig" "$out/contract.tsv" > "$out/AtomaProof.v"
bash "$root/scripts/atoma-scalar-capsule.sh" "$out/source.zig" "$out/contract.tsv" "$out/AtomaProof.v"
cd "$out"
coqc --version > coqc-version.txt
case $(head -n 1 coqc-version.txt) in
    'The Coq Proof Assistant, version 8.18.0'|'The Rocq Prover, version 9.2') ;;
    *) fail 'unsupported Coq/Rocq profile' ;;
esac
timeout -k 5 120 coqc -q ScalarSource.v > library-assumptions.txt 2>&1
[[ $(grep -c '^Closed under the global context$' library-assumptions.txt) == 2 ]]
checker_digest=$(sha256sum ScalarSource.vo)
timeout -k 5 120 echidna prove "$out/AtomaProof.v" --prover coq --timeout 90 --output json > echidna.json 2> echidna.stderr \
    || fail 'ECHIDNA did not verify the source interpretation'
jq -e -s --arg goal "$out/AtomaProof.v" '
    length == 1 and (.[0] | .schema == "echidna.prove.result/1" and
    .status == "verified" and .prover == "Coq" and .goal == $goal and
    .trust.axioms == [] and .trust.confidence == null)' echidna.json >/dev/null
[[ -s AtomaProof.vo ]] || fail 'missing compiled proof'
[[ $(sha256sum ScalarSource.vo) == "$checker_digest" ]] || fail 'backend changed the independently compiled source checker'
timeout -k 5 120 coqchk -silent -Q . '' ScalarSource AtomaProof > coqchk.txt 2>&1
"$ATOMA" scalar-coq-audit source.zig contract.tsv > Audit.v
bash "$root/scripts/atoma-scalar-capsule.sh" source.zig contract.tsv Audit.v
timeout -k 5 120 coqc -q -Q . '' Audit.v > assumptions.txt 2>&1
[[ $(grep -c '^Closed under the global context$' assumptions.txt) == 2 ]] || fail 'unexpected assumption closure'
! grep -q '^Axioms:' assumptions.txt
cmp -s source.zig "$source_path" || fail 'source changed during replay'
cmp -s contract.tsv "$table_path" || fail 'contract changed during replay'
cmp -s ScalarSource.v "$root/verification/atoma/consumer/coq/ScalarSource.v" || fail 'checker changed during replay'
bash "$root/scripts/atoma-scalar-capsule.sh" source.zig contract.tsv AtomaProof.v
sha256sum source.zig contract.tsv ScalarSource.v ScalarSource.vo AtomaProof.v AtomaProof.vo Audit.v Audit.vo echidna.json coqchk.txt assumptions.txt > inputs.sha256
for tool in "$ATOMA" echidna coqc coqchk; do sha256sum "$(command -v "$tool")"; done > tools.sha256
jq -cnS --arg source "$(sha256sum source.zig | cut -d ' ' -f 1)" \
    --arg contract "$(sha256sum contract.tsv | cut -d ' ' -f 1)" \
    '{schema:"atoma.scalar.source/1",status:"INCOMPLETE",scope:"closed scalar source interpretation",
      source_sha256:$source,contract_sha256:$contract,inputs:256,source_parser:"checked-in-Coq",
      coqchk:"checked",assumptions:[],compiler_refinement:"unproved",
      contract_authority:"caller must bind the table producer; see consumer evidence"}' > receipt.json
echo 'SCALAR-SOURCE-CHECKED: original bytes independently interpreted; compiler and foreign-boundary obligations remain'
