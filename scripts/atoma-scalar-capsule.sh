#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Independently bind the emitted literal bytes/table to the original inputs.
set -euo pipefail
[[ $# == 3 ]] || { echo 'usage: atoma-scalar-capsule.sh SOURCE TABLE PROOF' >&2; exit 2; }
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT
{
    printf 'Definition source_bytes : list nat := ['
    od -An -v -tu1 "$1" | awk '{for(i=1;i<=NF;i++){printf "%s%s", sep, $i; sep="; "}}'
    printf '].\nDefinition specification : list N := ['
    awk 'NF != 2 || $1 !~ /^[0-9]+$/ || $2 !~ /^[0-9]+$/ || $1 != NR-1 {exit 1}
         {printf "%s%s%%N", sep, $2; sep="; "} END {if(NR != 256) exit 1}' "$2"
    printf '].\n'
} > "$expected"
grep '^Definition \(source_bytes\|specification\) :' "$3" > "$actual"
cmp -s "$expected" "$actual" || { echo 'SCALAR-REFUSED: capsule differs from source/contract bytes' >&2; exit 1; }
