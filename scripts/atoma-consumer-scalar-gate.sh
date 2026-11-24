#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Hosted CI only: fresh Idris contracts, actual consumer source, native witnesses.
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
evidence_root="$root/build/atoma-evidence/scalar-consumers"
mkdir -p "$evidence_root"
out=$(mktemp -d "$evidence_root/run.XXXXXXXX")
echo "Scalar consumer evidence: $out"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for tool in git idris2 zig coqc coqchk echidna jq; do command -v "$tool" >/dev/null; done
[[ $(zig version) == 0.15.2 ]]
idris2 --version > "$out/idris-version.txt"
zig env > "$out/zig-environment.json"
cp "$root/tests/consumer-scalar/consumers.tsv" "$out/"

while read -r repo revision helper oracle extra; do
    [[ $repo == \#* || -z $repo ]] && continue
    [[ -z ${extra:-} && $revision =~ ^[0-9a-f]{40}$ ]]
    case "$repo" in proven|unified-api-adapter) ;; *) exit 1 ;; esac
    checkout="$work/$repo"
    git init -q "$checkout"
    git -C "$checkout" remote add origin "https://github.com/hyperpolymath/$repo.git"
    git -C "$checkout" fetch -q --depth 1 origin "$revision"
    git -C "$checkout" checkout -q --detach FETCH_HEAD
    [[ $(git -C "$checkout" rev-parse HEAD) == "$revision" ]]
    evidence="$out/$repo"
    mkdir "$evidence"
    run="$work/$repo-run"
    mkdir "$run"
    cp "$checkout/$helper" "$run/source.zig"
    cp "$checkout/$oracle" "$run/Main.idr"
    if [[ $repo == proven ]]; then
        mkdir -p "$run/Proven/FFI"
        cp "$checkout/src/Proven/FFI/RefCBits8.idr" "$run/Proven/FFI/"
        cp "$checkout/ffi/zig/src/refc/bits8.zig" "$evidence/consumer-wrapper.zig"
        call='source.encodeWord(byte)'
        mutation='s/| 1/| 0/'
    else
        cp -R "$checkout/src/interface/Abi" "$run/"
        cp "$checkout/src/interface/ffi/src/registry.zig" "$evidence/consumer-wrapper.zig"
        call='@as(u64, @intFromBool(source.known(byte)))'
        mutation='s/<= 9/<= 10/'
    fi
    (
        cd "$run"
        find . -name '*.idr' -print0 | LC_ALL=C sort -z | xargs -0 sha256sum
        sha256sum source.zig
    ) > "$evidence/inputs.sha256"
    (cd "$run"; idris2 --total -Werror --codegen refc -o oracle Main.idr) > "$evidence/idris-build.txt" 2>&1 || {
        cat "$evidence/idris-build.txt" >&2; exit 1;
    }
    if grep -q '^Error:' "$evidence/idris-build.txt"; then cat "$evidence/idris-build.txt" >&2; exit 1; fi
    [[ -x "$run/build/exec/oracle" ]]
    (cd "$run"; printf ':m\n:q\n' | idris2 --no-banner Main.idr) > "$evidence/idris-holes.txt" 2>&1
    grep -q 'No holes' "$evidence/idris-holes.txt"
    if grep -q '^Error:' "$evidence/idris-holes.txt"; then cat "$evidence/idris-holes.txt" >&2; exit 1; fi
    "$run/build/exec/oracle" > "$evidence/contract.tsv"
    # A standalone pure Zig caller tests the compiled helper. No C FFI is added.
    cat > "$run/runner.zig" <<ZIG
const std = @import("std");
const source = @import("source.zig");
pub fn main() !void {
    var buf: [96]u8 = undefined;
    for (0..256) |index| {
        const byte: u8 = @intCast(index);
        const line = try std.fmt.bufPrint(&buf, "{d} {d}\\n", .{index, $call});
        try std.fs.File.stdout().writeAll(line);
    }
}
ZIG
    for mode in Debug ReleaseSafe ReleaseFast ReleaseSmall; do
        zig build-exe "$run/runner.zig" -O "$mode" -femit-bin="$run/native-$mode" > "$evidence/zig-$mode.txt" 2>&1 || {
            cat "$evidence/zig-$mode.txt" >&2; exit 1;
        }
        "$run/native-$mode" > "$evidence/native-$mode.tsv"
        cmp "$evidence/contract.tsv" "$evidence/native-$mode.tsv"
    done
    bash "$root/scripts/atoma-scalar-replay.sh" "$run/source.zig" "$evidence/contract.tsv" "$evidence/replay"
    # Compile the wrong body successfully, then require an observable mismatch.
    sed "$mutation" "$run/source.zig" > "$run/mutant.zig"
    ! cmp -s "$run/source.zig" "$run/mutant.zig"
    cp "$run/source.zig" "$run/original.zig"
    cp "$run/mutant.zig" "$run/source.zig"
    zig build-exe "$run/runner.zig" -O ReleaseSafe -femit-bin="$run/mutant" > "$evidence/mutant-build.txt" 2>&1
    "$run/mutant" > "$evidence/mutant.tsv"
    if cmp -s "$evidence/contract.tsv" "$evidence/mutant.tsv"; then
        echo "FAIL native mutation survived: $repo" >&2; exit 1
    fi
    if bash "$root/scripts/atoma-scalar-replay.sh" "$run/source.zig" "$evidence/contract.tsv" "$evidence/rejected-mutant" > "$evidence/mutant-replay.txt" 2>&1; then
        echo "FAIL source mutation proved: $repo" >&2; exit 1
    fi
    grep -q 'ECHIDNA did not verify' "$evidence/mutant-replay.txt"
    cp "$run/original.zig" "$run/source.zig"
    (cd "$run"; sha256sum -c "$evidence/inputs.sha256") > "$evidence/recheck.txt"
    jq -cnS --arg repo "$repo" --arg revision "$revision" --arg helper "$helper" --arg oracle "$oracle" \
      '{schema:"atoma.consumer.scalar/1",status:"INCOMPLETE",repository:$repo,revision:$revision,
        helper:$helper,oracle:$oracle,inputs:256,contract:"fresh total Idris2 RefC oracle; no holes",
        native_modes:["Debug","ReleaseSafe","ReleaseFast","ReleaseSmall"],
        replay:"original bytes interpreted in Coq; ECHIDNA plus coqchk and assumption audit",
        open:["Zig compiler refinement","Idris primitive/compiler correspondence","pointer leases","whole-wrapper effects"]}' > "$evidence/receipt.json"
    printf 'CONSUMER-SCALAR-CHECKED %s %s\n' "$repo" "$revision"
done < "$root/tests/consumer-scalar/consumers.tsv"
bash "$root/scripts/atoma-scalar-replay-falsifiers.sh" "$out/proven/replay/source.zig" \
    "$out/proven/contract.tsv" "$out/replay-falsifiers"
echo 'CONSUMER SCALARS PASS: source interpretation and native witnesses; full boundary remains INCOMPLETE'
