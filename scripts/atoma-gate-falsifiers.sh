#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Exercise the gate's failure paths in a disposable tree, never the checkout.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/examples/atoma/frame-v1" "$tmp/tools/atoma/src" "$tmp/tools/atoma/zig-out/bin"
cp "$root/examples/atoma/frame-v1/verify.sh" "$tmp/examples/atoma/frame-v1/"
gate="$tmp/examples/atoma/frame-v1/verify.sh"
for name in ZIG Z3 AGDA IDRIS2; do
    if env "$name=$tmp/absent-$name" bash "$gate" > "$tmp/out" 2>&1; then
        echo "FAIL missing $name reported success"; exit 1
    fi
    grep -q "FAIL missing required tool: $tmp/absent-$name" "$tmp/out"
    echo "falsifier PASS missing $name rejected"
done
cp "$root/tools/atoma/build.zig" "$tmp/tools/atoma/"
cp "$root/tools/atoma/src/"*.zig "$tmp/tools/atoma/src/"
printf '\nthis is not Zig;\n' >> "$tmp/tools/atoma/src/main.zig"
printf '#!/bin/sh\necho STALE-BINARY-USED\nexit 0\n' > "$tmp/tools/atoma/zig-out/bin/atoma"
chmod +x "$tmp/tools/atoma/zig-out/bin/atoma"
if bash "$gate" > "$tmp/out" 2>&1; then
    echo 'FAIL stale binary hid a broken current source'; exit 1
fi
grep -q 'FAIL cannot build current atoma' "$tmp/out"
if grep -q STALE-BINARY-USED "$tmp/out"; then
    echo 'FAIL executed stale binary'; exit 1
fi
echo 'falsifier PASS stale executable cannot bypass current-source build'

# A plausible stdout verdict must not hide a failed solver process. Reuse the
# real preceding gates in the disposable tree so the observed failure is G7.
cp "$root/tools/atoma/src/main.zig" "$tmp/tools/atoma/src/"
cp -a "$root/examples/atoma/frame-v1/." "$tmp/examples/atoma/frame-v1/"
mkdir -p "$tmp/scripts"
cp "$root/scripts/atoma-check-idris.sh" "$tmp/scripts/"
printf '#!/bin/sh\nprintf "unsat\\n"\nexit 1\n' > "$tmp/failed-z3"
chmod +x "$tmp/failed-z3"
if Z3="$tmp/failed-z3" bash "$gate" > "$tmp/out" 2>&1; then
    echo 'FAIL solver failure accepted as unsat'; exit 1
fi
grep -q 'FAIL G7 solver process failed:' "$tmp/out"
echo 'falsifier PASS solver stdout cannot hide a failed process'

atoma="$root/tools/atoma/zig-out/bin/atoma"
printf 'export fn broken(' > "$tmp/syntax.zig"
truncate -s 16777217 "$tmp/too-large.zig"
for command in source-check source-vc; do
    for input in absent.zig syntax.zig too-large.zig; do
        rc=0
        "$atoma" "$command" "$tmp/$input" > "$tmp/out" 2>&1 || rc=$?
        [[ "$rc" == 3 ]] || { echo "FAIL $command $input exit=$rc, expected I/O/parse exit 3"; exit 1; }
    done
done
rc=0
"$atoma" source-vc "$root/examples/atoma/source-u8/increment.zig" > /dev/full 2> "$tmp/out" || rc=$?
[[ "$rc" == 3 ]] || { echo "FAIL output write error exit=$rc, expected 3"; exit 1; }
grep -q SOURCE-IO-ERROR "$tmp/out"
echo 'falsifier PASS source command input/output errors are distinct from verification failures'

mkdir -p "$tmp/verification/atoma/agda" "$tmp/verification/proofs/agda"
cp "$root/verification/atoma/check-agda.sh" "$tmp/verification/atoma/"
: > "$tmp/verification/proofs/agda/MANIFEST"
if bash "$tmp/verification/atoma/check-agda.sh" > "$tmp/out" 2>&1; then
    echo 'FAIL empty Agda registry accepted'; exit 1
fi
grep -q 'FAIL no registered Atoma Agda modules' "$tmp/out"
echo 'falsifier PASS empty Agda registry rejected'
