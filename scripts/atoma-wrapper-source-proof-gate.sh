#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/scalar-proof-evidence/wrapper-source"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 45 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
cp "$root/verification/atoma/consumer/coq/"{ScalarSource,RegistrySource,WrapperSource}.v "$work/"
fetch() {
  local repo=$1 revision=$2 path=$3 target=$4
  [[ $revision =~ ^[0-9a-f]{40}$ ]]
  curl --proto '=https' --proto-redir '=https' --connect-timeout 20 --max-time 120 -fsSL --retry 1 \
    "https://raw.githubusercontent.com/hyperpolymath/$repo/$revision/$path" -o "$target"
}
proven=$(cat "$root/tests/consumer-word/ownership-proven.pin")
uaa=$(cat "$root/tests/consumer-word/ownership-uaa.pin")
fetch proven "$proven" ffi/zig/src/header_refc.zig "$work/header.zig"
fetch proven "$proven" ffi/zig/src/refc/bits8.zig "$work/bits8.zig"
fetch unified-api-adapter "$uaa" src/interface/ffi/src/registry.zig "$work/registry.zig"
fetch unified-api-adapter "$uaa" src/interface/ffi/src/registry_state.zig "$work/registry_state.zig"
fetch unified-api-adapter "$uaa" src/interface/ffi/src/protocol_tag.zig "$work/protocol_tag.zig"
cd "$work"
for library in ScalarSource RegistrySource WrapperSource; do
  coqc -q "$library.v" > "$out/$library.txt" 2>&1
done
[[ $(grep -c '^Closed under the global context$' "$out/WrapperSource.txt") == 7 ]]
for profile in registry header; do
  dependency=registry_state.zig; [[ $profile != header ]] || dependency=bits8.zig
  bash "$root/scripts/atoma-wrapper-capsule.sh" "$profile" "$profile.zig" "$dependency" protocol_tag.zig > AtomaProof.v
  coqc -q AtomaProof.v > "$out/$profile.txt" 2>&1
  coqchk -silent -Q . '' WrapperSource AtomaProof > "$out/$profile-coqchk.txt" 2>&1
  cp AtomaProof.v "$out/$profile-capsule.v"
done
reject() {
  local name=$1 profile=$2 dependency=$3
  bash "$root/scripts/atoma-wrapper-capsule.sh" "$profile" mutant.zig "$dependency" protocol_tag.zig > Bad.v
  if coqc -q Bad.v > "$out/reject-$name.txt" 2>&1; then echo "FAIL $name accepted" >&2; exit 1; fi
  grep -q 'Unable to unify' "$out/reject-$name.txt"
}
for mutation in cleanup context order span; do
  case "$mutation" in
    cleanup) sed '/defer registry\.\* = state.finish/d' registry.zig ;;
    context) sed 's/endpoint.callback(endpoint.context, bytes, len)/endpoint.callback(null, bytes, len)/' registry.zig ;;
    order) sed 's/registry\.\* = reply.next;/registry.* = state.finish(Endpoint, reply.next);/' registry.zig ;;
    span) sed '/if (bytes == null and len != 0) return 4;/d' registry.zig ;;
  esac > mutant.zig
  if cmp -s registry.zig mutant.zig; then echo 'FAIL unchanged registry mutant' >&2; exit 1; fi
  reject "$mutation" registry registry_state.zig
done
for mutation in initial bound final import; do
  case "$mutation" in
    initial) sed 's/var state: u8 = 0/var state: u8 = 1/' header.zig ;;
    bound) sed 's/next > 1/next > 2/' header.zig ;;
    final) sed 's/return state == 1/return state == 0/' header.zig ;;
    import) sed 's@refc/bits8.zig@refc/ bits8.zig@' header.zig ;;
  esac > mutant.zig
  if cmp -s header.zig mutant.zig; then echo 'FAIL unchanged header mutant' >&2; exit 1; fi
  reject "$mutation" header bits8.zig
done
sha256sum ./*.v ./*.zig > "$out/inputs.sha256"
cp ./*.zig "$out/"
echo 'WRAPPER SOURCE PASS: conditional frame and borrowed loop; machine pointer and foreign-call premises remain'
