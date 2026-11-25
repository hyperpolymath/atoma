#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Independent replay of original source bytes; no submitted AST or verdict.
set -euo pipefail
[[ $# == 4 ]] || { echo 'usage: source-replay PROFILE SOURCE IMPORT_OR_DASH NEW_DIRECTORY' >&2; exit 2; }
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
profile=$1
source_path=$(realpath "$2")
out=$(realpath -m "$4")
fail() { echo "SOURCE-REPLAY-REFUSED: $*" >&2; exit 1; }
mkdir "$out" || fail 'evidence directory must be new'
cp "$source_path" "$out/source.zig"
case "$profile" in
  decoder)
    import_path=$(realpath "$3")
    cp "$import_path" "$out/encoder.zig"
    libraries=(ScalarSource CanonicalWord WordSource)
    reports=2
    ;;
  registry)
    [[ $3 == - ]] || exit 2
    libraries=(ScalarSource RegistrySource)
    reports=1
    ;;
  registry-wrapper|header-wrapper|registry-lifetime)
    import_path=$(realpath "$3")
    cp "$import_path" "$out/dependency.zig"
    libraries=(ScalarSource RegistrySource WrapperSource)
    reports=1
    if [[ $profile == registry-wrapper || $profile == registry-lifetime ]]; then
      protocol_path=$(dirname "$source_path")/protocol_tag.zig
      cp "$protocol_path" "$out/protocol_tag.zig"
      reports=3
    fi
    if [[ $profile == registry-lifetime ]]; then
      libraries+=(HeapOwnership RegistryLifetimeSource)
      reports=6
    fi
    ;;
  public-header)
    import_path=$(realpath "$3")
    cp "$import_path" "$out/dependency.zig"
    backend_path=$(dirname "$source_path")/header_refc.zig
    cp "$backend_path" "$out/backend.zig"
    libraries=(ScalarSource RegistrySource WrapperSource HeapOwnership HeaderBoundaryContext HeaderBoundarySource)
    reports=4
    ;;
  *) fail 'unsupported source profile' ;;
esac
for library in "${libraries[@]}"; do
    cp "$root/verification/atoma/consumer/coq/$library.v" "$out/"
done
capsule() {
    case "$profile" in
      decoder) bash "$root/scripts/atoma-word-capsule.sh" "$out/source.zig" "$out/encoder.zig" ;;
      registry) bash "$root/scripts/atoma-registry-capsule.sh" "$out/source.zig" ;;
      registry-wrapper) bash "$root/scripts/atoma-wrapper-capsule.sh" registry "$out/source.zig" "$out/dependency.zig" "$out/protocol_tag.zig" ;;
      header-wrapper) bash "$root/scripts/atoma-wrapper-capsule.sh" header "$out/source.zig" "$out/dependency.zig" - ;;
      registry-lifetime) bash "$root/scripts/atoma-registry-lifetime-capsule.sh" "$out/source.zig" "$out/dependency.zig" "$out/protocol_tag.zig" ;;
      public-header) bash "$root/scripts/atoma-public-header-capsule.sh" "$out/source.zig" "$out/dependency.zig" "$out/backend.zig" ;;
    esac
}
capsule > "$out/AtomaProof.v"
cd "$out"
for library in "${libraries[@]}"; do
    timeout -k 5 180 coqc -q "$library.v" > "$library-assumptions.txt" 2>&1
done
sha256sum ./*.v ./*.vo ./*.zig > before.sha256
timeout -k 5 180 echidna prove "$out/AtomaProof.v" --prover coq --timeout 150 --output json > echidna.json 2> echidna.stderr \
  || fail 'ECHIDNA did not verify the source interpretation'
jq -e -s --arg goal "$out/AtomaProof.v" '
  length == 1 and (.[0] | .schema == "echidna.prove.result/1" and
  .status == "verified" and .prover == "Coq" and .goal == $goal and
  .trust.axioms == [] and .trust.confidence == null)' echidna.json >/dev/null \
  || fail 'ECHIDNA result was malformed, untrusted or not bound to this capsule'
[[ -s AtomaProof.vo ]] || fail 'missing compiled proof'
sha256sum -c before.sha256 > recheck.txt || fail 'backend changed independent checker or source'
timeout -k 5 180 coqchk -silent -Q . '' "${libraries[@]}" AtomaProof > coqchk.txt 2>&1
capsule > Audit.v
cmp -s AtomaProof.v Audit.v || fail 'capsule differs from independent regeneration'
timeout -k 5 180 coqc -q Audit.v > assumptions.txt 2>&1
[[ $(grep -c '^Closed under the global context$' assumptions.txt) == "$reports" ]] || fail 'unexpected assumptions'
if grep -q '^Axioms:' assumptions.txt; then fail 'audit reported axioms'; fi
cmp -s source.zig "$source_path" || fail 'source changed during replay'
if [[ $profile == decoder ]]; then cmp -s encoder.zig "$import_path" || fail 'import changed'; fi
if [[ $profile == *-wrapper || $profile == registry-lifetime || $profile == public-header ]]; then cmp -s dependency.zig "$import_path" || fail 'entry dependency changed'; fi
if [[ $profile == registry-wrapper || $profile == registry-lifetime ]]; then cmp -s protocol_tag.zig "$protocol_path" || fail 'protocol dependency changed'; fi
if [[ $profile == public-header ]]; then cmp -s backend.zig "$backend_path" || fail 'header backend changed'; fi
for library in "${libraries[@]}"; do
    cmp -s "$library.v" "$root/verification/atoma/consumer/coq/$library.v" || fail 'checker changed'
done
sha256sum ./*.zig ./*.v ./*.vo echidna.json assumptions.txt coqchk.txt > inputs.sha256
for tool in coqc coqchk echidna; do sha256sum "$(command -v "$tool")"; done > tools.sha256
jq -cnS --arg profile "$profile" \
  '{schema:"atoma.source.profile/1",status:"INCOMPLETE",profile:$profile,
    checked:"original source interpretation; independent kernel replay",assumptions:[],
    open:["Zig parser/compiler refinement","Idris primitive/compiler correspondence",
      "cross-kernel witness transport","pointer validity and exclusive ownership",
      "foreign callback and RefC contracts","whole-wrapper effects outside admitted profile"]}' > receipt.json
echo "SOURCE-CHECKED $profile: interpreted source; compiler and foreign boundary remain explicit"
