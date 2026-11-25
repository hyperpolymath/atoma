#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
parent="$root/build/atoma-evidence/heap-consumers"
mkdir -p "$parent"
out=$(mktemp -d "$parent/run.XXXXXXXX")
work=$(mktemp -d)
echo INCOMPLETE > "$out/result.txt"
trap 'status=$?; if ((status)); then echo FAIL > "$out/result.txt"; fi; rm -rf "$work"' EXIT
for profile in public-header registry-lifetime; do
  if [[ $profile == public-header ]]; then
    repo=proven; pin=proven.pin
    source=ffi/zig/src/core.zig; dependency=ffi/zig/src/main_refc.zig
  else
    repo=unified-api-adapter; pin=uaa.pin
    source=src/interface/ffi/src/registry.zig; dependency=src/interface/ffi/src/registry_state.zig
  fi
  revision=$(cat "$root/tests/consumer-heap/$pin")
  [[ $revision =~ ^[0-9a-f]{40}$ ]]
  checkout="$work/$repo"
  git init -q "$checkout"
  git -C "$checkout" remote add origin "https://github.com/hyperpolymath/$repo.git"
  git -C "$checkout" fetch -q --depth 1 origin "$revision"
  git -C "$checkout" checkout -q --detach FETCH_HEAD
  [[ $(git -C "$checkout" rev-parse HEAD) == "$revision" ]]
  git -C "$checkout" diff --exit-code "$revision" --
  mkdir "$out/$profile"
  echo "$revision" > "$out/$profile/revision.txt"
  if [[ $profile == public-header ]]; then
    EVIDENCE_DIR="$out/$profile/native" bash "$checkout/scripts/test-header-bridge.sh"
    for marker in result.txt ownership/result.txt ownership-controls/result.txt boundary/result.txt boundary-controls/result.txt; do
      [[ $(cat "$out/$profile/native/$marker") == PASS ]]
    done
  else
    for slice in ownership ownership-controls lifetime lifetime-controls; do
      EVIDENCE_DIR="$out/$profile/$slice" bash "$checkout/scripts/check-registry-$slice.sh"
      [[ $(cat "$out/$profile/$slice/result.txt") == PASS ]]
    done
  fi
  git -C "$checkout" diff --exit-code "$revision" -- > "$out/$profile/native-recheck.txt"
  bash "$root/scripts/atoma-source-profile-replay.sh" "$profile" "$checkout/$source" "$checkout/$dependency" "$out/$profile/replay"
  git -C "$checkout" diff --exit-code "$revision" -- > "$out/$profile/replay-recheck.txt"
done
echo PASS > "$out/result.txt"
echo 'HEAP CONSUMERS PASS: actual public entry and registry lifetime profiles; native authority and lifetime correspondence remain premises'
