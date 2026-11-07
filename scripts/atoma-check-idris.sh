#!/usr/bin/env bash
# Typecheck the normative contract and QTT negatives, then execute its encoder.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
IDRIS2=${IDRIS2:-idris2}
command -v "$IDRIS2" >/dev/null || { echo "FAIL missing Idris2: $IDRIS2" >&2; exit 1; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
example="$root/examples/atoma/frame-v1"
cp "$example/abi/FrameAbi.ipkg" "$tmp/"
while IFS= read -r file; do
    rel=${file#"$example/abi/"}
    mkdir -p "$tmp/$(dirname "$rel")"
    cp "$file" "$tmp/$rel"
done < <(find "$example/abi" -name '*.idr' -not -path '*/build/*' | sort)
check() {
    if ! (cd "$tmp" && "$IDRIS2" "$@") > "$tmp/compiler.log" 2>&1; then
        cat "$tmp/compiler.log" >&2; return 1
    fi
    cat "$tmp/compiler.log"
    ! grep -q '^Error:' "$tmp/compiler.log"
}
check --typecheck FrameAbi.ipkg
while IFS= read -r file; do
    check --check "${file#"$tmp/"}"
done < <(find "$tmp" -name '*.idr' -not -path '*/build/*' | sort)
check -o extract Extract.idr
"$tmp/build/exec/extract" > "$tmp/face-a.cspec"
"$root/tools/atoma/zig-out/bin/atoma" equiv "$tmp/face-a.cspec" "$example/spec/face-a.cspec"
cp "$tmp/face-a.cspec" "$example/witness/face-a.extracted.cspec"
echo 'F0.1 ok: Idris2 contract, QTT negatives and executable Face A extraction'
