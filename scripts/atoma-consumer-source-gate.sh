#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
mkdir -p "$root/build/atoma-evidence/source-consumers"
out=$(mktemp -d "$root/build/atoma-evidence/source-consumers/run.XXXXXXXX")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for profile in decoder registry; do
    case "$profile" in
      decoder) repo=proven; pin=proven.pin; runner=scripts/test-refc-decoder.sh
        helper=ffi/zig/src/refc/bits8_decode_word.zig; wrapper=ffi/zig/src/refc/bits8.zig ;;
      registry) repo=unified-api-adapter; pin=uaa.pin; runner=scripts/check-registry-state.sh
        helper=src/interface/ffi/src/registry_state.zig; wrapper=src/interface/ffi/src/registry.zig ;;
    esac
    revision=$(cat "$root/tests/consumer-word/$pin")
    [[ $revision =~ ^[0-9a-f]{40}$ ]]
    checkout="$work/$repo"
    git init -q "$checkout"
    git -C "$checkout" remote add origin "https://github.com/hyperpolymath/$repo.git"
    git -C "$checkout" fetch -q --depth 1 origin "$revision"
    git -C "$checkout" checkout -q --detach FETCH_HEAD
    [[ $(git -C "$checkout" rev-parse HEAD) == "$revision" ]]
    mkdir "$out/$profile"
    echo "$revision" > "$out/$profile/revision.txt"
    cp "$checkout/$wrapper" "$out/$profile/consumer-wrapper.zig"
    EVIDENCE_DIR="$out/$profile/native" bash "$checkout/$runner"
    [[ $(cat "$out/$profile/native/result.txt") == PASS ]]
    if [[ $profile == decoder ]]; then
        imported="$checkout/ffi/zig/src/refc/bits8_word.zig"
        cmp "$checkout/$helper" "$out/$profile/native/bits8_decode_word.zig"
        cmp "$imported" "$out/$profile/native/bits8_word.zig"
    else
        imported=-
        cmp "$checkout/$helper" "$out/$profile/native/registry_state.zig"
    fi
    bash "$root/scripts/atoma-source-profile-replay.sh" "$profile" "$checkout/$helper" "$imported" "$out/$profile/replay"
    (cd "$checkout"; sha256sum "$helper" "$wrapper" "$runner") > "$out/$profile/consumer-inputs.sha256"
done
[[ -s "$out/decoder/replay/receipt.json" && -s "$out/registry/replay/receipt.json" ]]
echo 'SOURCE CONSUMERS PASS: fresh Idris2 authority, actual Zig helpers, native controls and independent replay'

