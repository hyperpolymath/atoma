#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
mkdir -p "$root/build/atoma-evidence/wrapper-consumers"
out=$(mktemp -d "$root/build/atoma-evidence/wrapper-consumers/run.XXXXXXXX")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for profile in header registry; do
  if [[ $profile == header ]]; then
    repo=proven; pin=ownership-proven.pin
    source=ffi/zig/src/header_refc.zig; dependency=ffi/zig/src/refc/bits8.zig
  else
    repo=unified-api-adapter; pin=ownership-uaa.pin
    source=src/interface/ffi/src/registry.zig; dependency=src/interface/ffi/src/registry_state.zig
  fi
  revision=$(cat "$root/tests/consumer-word/$pin")
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
  if [[ $profile == header ]]; then
    EVIDENCE_DIR="$out/$profile/native" bash "$checkout/scripts/test-header-bridge.sh"
    [[ $(cat "$out/$profile/native/result.txt") == PASS ]]
    [[ $(cat "$out/$profile/native/ownership/result.txt") == PASS ]]
    [[ $(cat "$out/$profile/native/ownership-controls/result.txt") == PASS ]]
  else
    EVIDENCE_DIR="$out/$profile/native" bash "$checkout/scripts/check-registry-ownership.sh"
    [[ $(cat "$out/$profile/native/result.txt") == PASS ]]
    EVIDENCE_DIR="$out/$profile/native-controls" bash "$checkout/scripts/check-registry-ownership-controls.sh"
    [[ $(cat "$out/$profile/native-controls/result.txt") == PASS ]]
  fi
  git -C "$checkout" diff --exit-code "$revision" -- > "$out/$profile/consumer-recheck.txt"
  bash "$root/scripts/atoma-source-profile-replay.sh" "$profile-wrapper" "$checkout/$source" "$checkout/$dependency" "$out/$profile/replay"
  git -C "$checkout" diff --exit-code "$revision" -- > "$out/$profile/post-replay-recheck.txt"
done
echo 'WRAPPER CONSUMERS PASS: fresh native qualification and conditional original-source replay; ownership premises remain'
