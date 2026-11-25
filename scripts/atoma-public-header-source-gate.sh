#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/heap-source-evidence/public-header"
mkdir -p "$out"
echo INCOMPLETE > "$out/result.txt"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then echo FAIL > "$out/result.txt"; tail -n 40 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
libraries=(ScalarSource RegistrySource WrapperSource HeapOwnership HeaderBoundaryContext HeaderBoundarySource)
revision=$(cat "$root/tests/consumer-heap/proven.pin")
[[ $revision =~ ^[0-9a-f]{40}$ ]]
echo "$revision" > "$out/revision.txt"
sha256sum "$root/scripts/atoma-public-header-source-gate.sh" "$root/scripts/atoma-public-header-capsule.sh" \
  "$root/tests/consumer-heap/proven.pin" > "$out/inputs.sha256"
for library in "${libraries[@]}"; do
  sha256sum "$root/verification/atoma/consumer/coq/$library.v" >> "$out/inputs.sha256"
  cp "$root/verification/atoma/consumer/coq/$library.v" "$work/"
  cmp "$root/verification/atoma/consumer/coq/$library.v" "$work/$library.v"
done
for source in core main_refc header_refc; do
  curl --proto '=https' --proto-redir '=https' --connect-timeout 20 --max-time 120 -fsSL --retry 1 \
    "https://raw.githubusercontent.com/hyperpolymath/proven/$revision/ffi/zig/src/$source.zig" -o "$work/$source.zig"
done
sha256sum -c "$out/inputs.sha256" > "$out/snapshot-recheck.txt"
cd "$work"
bash "$root/scripts/atoma-public-header-capsule.sh" core.zig main_refc.zig header_refc.zig > AtomaProof.v
sha256sum ./*.v ./*.zig > "$out/checked-inputs.sha256"
for library in "${libraries[@]}"; do coqc -q "$library.v" > "$out/$library.txt" 2>&1; done
[[ $(grep -c '^Closed under the global context$' "$out/HeaderBoundarySource.txt") == 5 ]]
coqc -q AtomaProof.v > "$out/capsule.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/capsule.txt") == 4 ]]
if grep -q '^Axioms:' "$out/capsule.txt" "$out/HeaderBoundarySource.txt"; then echo 'FAIL public header assumptions' >&2; exit 1; fi
coqchk -silent -Q . '' "${libraries[@]}" AtomaProof > "$out/coqchk.txt" 2>&1
reject() {
  local name=$1 core=core.zig exports=main_refc.zig backend=header_refc.zig
  case "$2" in core) core=mutant.zig ;; export) exports=mutant.zig ;; backend) backend=mutant.zig ;; *) exit 2 ;; esac
  bash "$root/scripts/atoma-public-header-capsule.sh" "$core" "$exports" "$backend" > Bad.v
  if coqc -q Bad.v > "$out/reject-$name.txt" 2>&1; then echo "FAIL $name source accepted" >&2; exit 1; fi
  grep -q 'Unable to unify' "$out/reject-$name.txt"
}
for mutation in slice null_status error_class null_order name context_status; do
  case "$mutation" in
    slice) sed '/^pub fn headerHasCrlf/,/^}/s/p\[0\.\.len\]/p[1..len]/' core.zig ;;
    null_status) sed '/^pub fn headerHasCrlf/,/^}/s/status = PROVEN_ERR_NULL_POINTER/status = PROVEN_OK/' core.zig ;;
    error_class) sed '/^pub fn headerHasCrlf/,/^}/s/) -99 else -7/) -7 else -99/' core.zig ;;
    null_order) awk '{print} /^pub fn headerHasCrlf/ {print "    if (ptr == null) _ = header_backend.detect(&.{}) catch false;"}' core.zig ;;
    name) sed 's/pub fn headerHasCrlf(/pub fn headerChanged(/' core.zig ;;
    context_status) sed 's/const PROVEN_ERR_NULL_POINTER: c_int = -1;/const PROVEN_ERR_NULL_POINTER: c_int = -2;/' core.zig ;;
  esac > mutant.zig
  if cmp -s core.zig mutant.zig; then echo 'FAIL unchanged public-entry mutant' >&2; exit 1; fi
  reject "$mutation" core
done
for mutation in forwarding import; do
  case "$mutation" in
    forwarding) sed '/^pub export fn proven_header_has_crlf/,/^}/s/, ptr, len)/, ptr, 0)/' main_refc.zig ;;
    import) sed 's/header_refc.zig/header_unavailable.zig/' main_refc.zig ;;
  esac > mutant.zig
  if cmp -s main_refc.zig mutant.zig; then echo 'FAIL unchanged public-export mutant' >&2; exit 1; fi
  reject "$mutation" export
done
sed 's/next > 1/next > 2/' header_refc.zig > mutant.zig
if cmp -s header_refc.zig mutant.zig; then echo 'FAIL unchanged backend mutant' >&2; exit 1; fi
reject backend backend
sha256sum -c "$out/checked-inputs.sha256" > "$out/checked-input-recheck.txt"
sha256sum -c "$out/inputs.sha256" > "$out/input-recheck.txt"
cp ./*.v ./*.vo core.zig main_refc.zig header_refc.zig "$out/"
echo PASS > "$out/result.txt"
echo 'PUBLIC HEADER SOURCE PASS: closed original entry/export and checked backend; readable live region and compiler premises remain'
