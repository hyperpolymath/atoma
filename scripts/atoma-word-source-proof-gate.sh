#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/build/scalar-proof-evidence/word-source"
mkdir -p "$out"
work=$(mktemp -d)
trap 'status=$?; if ((status)); then tail -n 60 "$out"/*.txt >&2; fi; rm -rf "$work"' EXIT
revision=$(cat "$root/tests/consumer-word/proven.pin")
[[ $revision =~ ^[0-9a-f]{40}$ ]]
printf '%s\n' "$revision" > "$out/proven.pin"
for file in bits8_decode_word.zig bits8_word.zig; do
    curl --proto '=https' --proto-redir '=https' -fL --retry 2 --connect-timeout 20 --max-time 120 \
      "https://raw.githubusercontent.com/hyperpolymath/proven/$revision/ffi/zig/src/refc/$file" -o "$out/$file"
done
cp "$root/verification/atoma/consumer/coq/"{ScalarSource,CanonicalWord,WordSource}.v "$work/"
cd "$work"
coqc -q ScalarSource.v > "$out/scalar-assumptions.txt" 2>&1
coqc -q CanonicalWord.v > "$out/word-assumptions.txt" 2>&1
coqc -q WordSource.v > "$out/source-assumptions.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/source-assumptions.txt") == 3 ]]
bash "$root/scripts/atoma-word-capsule.sh" "$out/bits8_decode_word.zig" "$out/bits8_word.zig" > AtomaWord.v
coqc -q AtomaWord.v > "$out/checked.txt" 2>&1
[[ $(grep -c '^Closed under the global context$' "$out/checked.txt") == 2 ]]
coqchk -silent -Q . '' ScalarSource CanonicalWord WordSource AtomaWord > "$out/coqchk.txt" 2>&1
cp AtomaWord.v "$out/"
reject() {
    local name=$1 decoder=$2 encoder=$3
    bash "$root/scripts/atoma-word-capsule.sh" "$decoder" "$encoder" > Bad.v
    if coqc -q Bad.v > "$out/reject-$name.txt" 2>&1; then
        echo "FAIL accepted $name" >&2; exit 1
    fi
    grep -q 'Unable to unify' "$out/reject-$name.txt"
}
for mutation in bound equality cast divisor import; do
    case "$mutation" in
      bound) sed '/if (payload > 255)/d' "$out/bits8_decode_word.zig" ;;
      equality) sed '/if (raw != word.encodeWord(byte))/d' "$out/bits8_decode_word.zig" ;;
      cast) sed 's/@intCast(payload)/@truncate(payload)/' "$out/bits8_decode_word.zig" ;;
      divisor) sed 's@/ 4294967296@/ 2147483648@' "$out/bits8_decode_word.zig" ;;
      import) sed 's/bits8_word.zig/other_word.zig/' "$out/bits8_decode_word.zig" ;;
    esac > "$work/$mutation.zig"
    reject "$mutation" "$work/$mutation.zig" "$out/bits8_word.zig"
done
sed 's/| 1/| 0/' "$out/bits8_word.zig" > tag.zig
reject encoder-tag "$out/bits8_decode_word.zig" tag.zig
sed 's/encodeWord/otherName/' "$out/bits8_word.zig" > renamed.zig
reject encoder-export "$out/bits8_decode_word.zig" renamed.zig
sed 's/bits8_word.zig/bits8_word .zig/' "$out/bits8_decode_word.zig" > import-space.zig
reject literal-whitespace import-space.zig "$out/bits8_word.zig"
printf '\nconst extra = @import("unbound.zig");\n' >> renamed.zig
reject trailing-import "$out/bits8_decode_word.zig" renamed.zig
sha256sum "$out/"*.zig ./*.v > "$out/inputs.sha256"
echo 'WORD SOURCE PASS: universal guarded source interpretation; pointer/compiler boundaries remain explicit'
