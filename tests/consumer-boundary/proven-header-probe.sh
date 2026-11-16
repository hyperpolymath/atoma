#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Execute the actual Idris predicate and Zig export, not handwritten oracles.
# A disagreement is exit 1. This is a diagnostic, not a proof certificate.
set -euo pipefail
proven=${1:?usage: proven-header-probe.sh /path/to/proven}
proven=$(cd "$proven" && pwd)
zig=${ZIG:-zig}
idris=${IDRIS2:-idris2}
command -v "$zig" >/dev/null
command -v "$idris" >/dev/null
evidence=${EVIDENCE_DIR:-$(mktemp -d -t atoma-header-evidence.XXXXXXXX)}
mkdir -p "$evidence"
evidence=$(cd "$evidence" && pwd)
work=$(mktemp -d -t atoma-header-probe.XXXXXXXX)
trap 'rm -rf -- "$work"' EXIT
mkdir "$work/src"
cp -R "$proven/src/Proven" "$work/src/Proven"
{
  git -C "$proven" rev-parse HEAD
  "$idris" --version
  "$zig" version
  git -C "$proven" diff --stat
  sha256sum "$proven/src/Proven/SafeHeader/Types.idr" "$proven/src/Proven/Core.idr" "$proven/src/Proven/SafeHeader/ByteKernel.idr" "$proven/ffi/zig/src/core.zig" "$proven/ffi/zig/src/header_refc.zig" "$proven/ffi/zig/src/main_refc.zig"
} > "$evidence/inputs.log"
cat > "$work/src/AtomaHeaderProbe.idr" <<'IDRIS'
module AtomaHeaderProbe
import Proven.SafeHeader.Types
main : IO ()
main = traverse_ (putStrLn . show . Proven.SafeHeader.Types.hasCRLF)
  ["\r", "\n", "\r\n", "clean", "a\rZ"]
IDRIS
(cd "$work"; "$idris" --source-dir src --codegen refc -o atoma-header-probe src/AtomaHeaderProbe.idr) > "$evidence/idris-build.log" 2>&1
if grep -q '^Error:' "$evidence/idris-build.log" || [[ ! -x "$work/build/exec/atoma-header-probe" ]]; then
  echo "FAIL: Idris RefC build; see $evidence" >&2; exit 2
fi
"$work/build/exec/atoma-header-probe" | tr '[:upper:]' '[:lower:]' > "$evidence/idris-results.txt"
cat > "$work/probe.zig" <<'ZIG'
const std = @import("std");
const Result = extern struct { status: c_int, value: bool };
extern fn proven_header_has_crlf(ptr: ?[*]const u8, len: usize) callconv(.c) Result;
pub fn main() !void {
    for ([_][]const u8{ "\r", "\n", "\r\n", "clean", "a\rZ" }) |bytes| {
        const r = proven_header_has_crlf(bytes.ptr, bytes.len);
        if (r.status != 0) return error.UnexpectedStatus;
        std.debug.print("{}\n", .{r.value});
    }
}
ZIG
IDRIS2="$idris" bash "$proven/scripts/build-header-refc.sh" "$work/bundle" > "$evidence/header-build.log" 2>&1
cp "$work/bundle/identity.log" "$evidence/header-identity.log"
(cd "$proven/ffi/zig"; "$zig" build --build-file build_standalone.zig -Dheader-refc="$work/bundle" --prefix "$work/install") > "$evidence/zig-build.log" 2>&1
"$zig" build-exe "$work/probe.zig" "$work/install/lib/libproven_ffi.a" "$work/bundle/libidris2_refc.a" "$work/bundle/libidris2_support.a" -lc -lgmp -lm -lpthread -femit-bin="$work/probe" >> "$evidence/zig-build.log" 2>&1
"$work/probe" > "$evidence/zig-results.txt" 2>&1
for result in idris-results.txt zig-results.txt; do
  if [[ $(wc -l < "$evidence/$result") -ne 5 ]] || grep -Evq '^(true|false)$' "$evidence/$result"; then
    echo "FAIL: malformed or incomplete executable results; see $evidence/$result" >&2
    exit 2
  fi
done
printf 'cr\nlf\ncrlf\nclean\nembedded-cr\n' > "$evidence/cases.txt"
paste "$evidence/cases.txt" "$evidence/idris-results.txt" "$evidence/zig-results.txt"
if ! diff -u "$evidence/idris-results.txt" "$evidence/zig-results.txt" > "$evidence/difference.log"; then
  echo "FAIL: Idris/RefC and Zig disagree; evidence: $evidence" >&2
  exit 1
fi
echo "PASS: these five executable cases agree; evidence: $evidence"
echo 'NOT A PROOF: source/compiler refinement, all inputs, pointer validity and full ABI correspondence remain separate obligations.'
