#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
parent="$root/build/heap-source-evidence/registry"
mkdir -p "$parent"
out=$(mktemp -d "$parent/run.XXXXXXXX")
work=$(mktemp -d)
echo INCOMPLETE > "$out/result.txt"
trap 'status=$?; if ((status)); then echo FAIL > "$out/result.txt"; tail -n 40 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
libraries=(ScalarSource RegistrySource WrapperSource HeapOwnership RegistryLifetimeSource)
sources=(scripts/atoma-registry-lifetime-source-gate.sh scripts/atoma-registry-lifetime-capsule.sh tests/consumer-heap/uaa.pin)
for library in "${libraries[@]}"; do sources+=("verification/atoma/consumer/coq/$library.v"); done
(cd "$root"; sha256sum "${sources[@]}") > "$out/source-inputs.sha256"
for library in "${libraries[@]}"; do
  cp "$root/verification/atoma/consumer/coq/$library.v" "$work/"
  cmp "$root/verification/atoma/consumer/coq/$library.v" "$work/$library.v"
done
revision=$(cat "$root/tests/consumer-heap/uaa.pin")
[[ $revision =~ ^[0-9a-f]{40}$ ]]
printf '%s\n' "$revision" > "$out/revision.txt"
for source in registry registry_state protocol_tag; do
  curl --proto '=https' --proto-redir '=https' --connect-timeout 20 --max-time 120 -fsSL --retry 1 \
    "https://raw.githubusercontent.com/hyperpolymath/unified-api-adapter/$revision/src/interface/ffi/src/$source.zig" -o "$work/$source.zig"
done
(cd "$root"; sha256sum -c "$out/source-inputs.sha256") > "$out/snapshot-recheck.txt"
cd "$work"
sha256sum ./*.v ./*.zig > "$out/checked-inputs.sha256"
for library in "${libraries[@]}"; do
  printf 'LIFETIME SOURCE: compiling %s\n' "$library"
  coqc -q "$library.v" > "$out/$library.txt" 2>&1
done
[[ $(grep -c '^Closed under the global context$' "$out/RegistryLifetimeSource.txt") == 4 ]]
bash "$root/scripts/atoma-registry-lifetime-capsule.sh" registry.zig registry_state.zig protocol_tag.zig > AtomaProof.v
coqc -q AtomaProof.v > "$out/capsule.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/capsule.txt") == 6 ]]
if grep -q '^Axioms:' "$out/capsule.txt"; then echo 'FAIL: lifetime capsule axioms' >&2; exit 1; fi
coqchk -silent -Q . '' "${libraries[@]}" AtomaProof > "$out/coqchk.txt" 2>&1
for mutation in remove-busy reorder-busy free-context clear-instead-free; do
  case "$mutation" in
    remove-busy)
      sed '/pub export fn uaa_registry_destroy/,/^}/ { /if (registry.active) return 6;/d; }' registry.zig > mutant.zig ;;
    reorder-busy)
      awk '/pub export fn uaa_registry_destroy/ {inside=1}
        inside && /if \(registry.active\) return 6;/ {next}
        {print}
        inside && /std.heap.c_allocator.destroy\(registry\);/ {print "    if (registry.active) return 6;"}
        inside && /^}/ {inside=0}' registry.zig > mutant.zig ;;
    free-context)
      sed 's/std.heap.c_allocator.destroy(registry);/std.heap.c_allocator.destroy(registry.rest.?.context);/' registry.zig > mutant.zig ;;
    clear-instead-free)
      sed 's/std.heap.c_allocator.destroy(registry);/registry.* = .{};/' registry.zig > mutant.zig ;;
  esac
  if cmp -s registry.zig mutant.zig; then echo "FAIL unchanged $mutation mutant" >&2; exit 1; fi
  bash "$root/scripts/atoma-registry-lifetime-capsule.sh" mutant.zig registry_state.zig protocol_tag.zig > Bad.v
  if coqc -q Bad.v > "$out/reject-$mutation.txt" 2>&1; then
    echo "FAIL $mutation accepted" >&2; exit 1
  fi
  grep -q 'Unable to unify' "$out/reject-$mutation.txt"
  cp mutant.zig "$out/$mutation.zig"
done
sha256sum -c "$out/checked-inputs.sha256" > "$out/checked-input-recheck.txt"
(cd "$root"; sha256sum -c "$out/source-inputs.sha256") > "$out/source-recheck.txt"
cp registry.zig registry_state.zig protocol_tag.zig AtomaProof.v AtomaProof.vo "$out/"
sha256sum AtomaProof.v AtomaProof.vo > "$out/capsule.sha256"
echo PASS > "$out/result.txt"
echo 'REGISTRY LIFETIME SOURCE PASS: parsed destroy guards and allocator effect; native pointer, caller authority and ghost-accounting premises remain'
