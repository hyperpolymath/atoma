#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Collect the compiler-witnessed layout rows for every target class into
# spec/layout.cspec. Deterministic: same compiler + same declaration ⇒ same
# bytes, in the same order (target order is fixed below).
#
# The rows are whatever the Zig compiler said. Nothing is computed here, and a
# declaration that does not hold makes the corresponding `zig build-obj` fail,
# which aborts the script (set -e).

set -eu
ZIG=${ZIG:-zig}
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
out="$here/../spec/layout.cspec"
tmp="$out.tmp"

: > "$tmp"
for triple in x86_64-linux-gnu aarch64-linux-gnu riscv64-linux-gnu wasm32-freestanding; do
    "$ZIG" build-obj "$here/layout_witness.zig" -target "$triple" -fno-emit-bin 2>&1 |
        sed -n 's/^@as(\*const \[[0-9]*:0\]u8, "\([^"]*\)")$/\1/p' |
        sed -n '/^\(field\|layout\) /p' >> "$tmp"
done
mv "$tmp" "$out"
printf 'layout.sh: %s rows -> %s\n' "$(wc -l < "$out" | tr -d ' ')" "spec/layout.cspec"
