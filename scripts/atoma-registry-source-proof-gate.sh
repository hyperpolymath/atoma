#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/scalar-proof-evidence/registry-source"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 60 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
revision=$(cat "$root/tests/consumer-word/uaa.pin")
[[ $revision =~ ^[0-9a-f]{40}$ ]]
printf '%s\n' "$revision" > "$out/uaa.pin"
curl --proto '=https' --proto-redir '=https' -fL --retry 2 --connect-timeout 20 --max-time 120 \
  "https://raw.githubusercontent.com/hyperpolymath/unified-api-adapter/$revision/src/interface/ffi/src/registry_state.zig" -o "$out/source.zig"
cp "$root/verification/atoma/consumer/coq/"{ScalarSource,RegistrySource}.v "$work/"
cd "$work"
coqc -q ScalarSource.v > "$out/scalar-assumptions.txt" 2>&1
coqc -q RegistrySource.v > "$out/registry-assumptions.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/registry-assumptions.txt") == 6 ]]
bash "$root/scripts/atoma-registry-capsule.sh" "$out/source.zig" > AtomaRegistry.v
coqc -q AtomaRegistry.v > "$out/checked.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/checked.txt") == 1 ]]
coqchk -silent -Q . '' ScalarSource RegistrySource AtomaRegistry > "$out/coqchk.txt" 2>&1
cp AtomaRegistry.v "$out/"
for mutation in selection frame busy restoration status identity import; do
    case "$mutation" in
      selection) sed 's/\.mcp => s.mcp/.mcp => s.rest/' "$out/source.zig" ;;
      frame) sed 's/\.rest = s.rest, .mcp = endpoint/.rest = endpoint, .mcp = endpoint/' "$out/source.zig" ;;
      busy) sed '/if (s.active)/d' "$out/source.zig" ;;
      restoration) sed 's/return mark(E, s, false)/return mark(E, s, true)/' "$out/source.zig" ;;
      status) sed 's/status <= 11/status <= 12/' "$out/source.zig" ;;
      identity) sed 's/\.selected = endpoint/.selected = null/' "$out/source.zig" ;;
      import) cat "$out/source.zig"; printf '\nconst hidden = @import("hidden.zig");\n' ;;
    esac > "$work/$mutation.zig"
    ! cmp -s "$work/$mutation.zig" "$out/source.zig"
    bash "$root/scripts/atoma-registry-capsule.sh" "$work/$mutation.zig" > Bad.v
    if coqc -q Bad.v > "$out/reject-$mutation.txt" 2>&1; then echo "FAIL accepted $mutation" >&2; exit 1; fi
    grep -q 'Unable to unify' "$out/reject-$mutation.txt"
done
sha256sum "$out/source.zig" ./*.v > "$out/inputs.sha256"
echo 'REGISTRY SOURCE PASS: opaque endpoint identities and state transitions; foreign ownership remains a premise'
