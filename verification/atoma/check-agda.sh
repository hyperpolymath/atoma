#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# check-agda.sh — typecheck the Atoma metatheory under the strictest flags.
#
#   agda --safe --without-K
#
# `--safe` rejects postulates, `{-# TERMINATING #-}`, `{-# NON_TERMINATING #-}`,
# `{-# REWRITE #-}`, cubical primitives and `primTrustMe`. `--without-K` rejects
# the K axiom. These flags do not establish that an exporter to Dedukti/CIC
# exists or preserves the theorem; that is a separate, currently open obligation.
#
# Exits 0 only if every module checks. Prints one line per module.

set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
AGDA=${AGDA:-agda}

cd "$here/agda"
command -v "$AGDA" >/dev/null 2>&1 || { echo "FAIL missing Agda: $AGDA" >&2; exit 1; }
# Check sources, even if a previous run left interface files behind.
rm -f ./*.agdai
trap 'rm -f ./*.agdai' EXIT

modules=$(awk -F '|' '$1 == "verification/atoma/agda" && $3 == "gated" {print $2}' "$here/../proofs/agda/MANIFEST")
[ -n "$modules" ] || { echo 'FAIL no registered Atoma Agda modules' >&2; exit 1; }
count=0
for m in $modules; do
    count=$((count + 1))
    if "$AGDA" --safe --without-K "$m" >/dev/null 2>&1; then
        printf 'agda ok   %s\n' "$m"
    else
        printf 'agda FAIL %s\n' "$m" >&2
        "$AGDA" --safe --without-K "$m" 2>&1 | sed -n '2,12p' >&2
        exit 1
    fi
done

# `--safe` already rejects these, but say so out loud: a reader should not have
# to trust that `--safe` means what the specification claims it means. This
# grep is belt-and-braces against a future flag change, not the primary gate.
if grep -nE '\bpostulate\b|\{!!\}|\{-#[[:space:]]*(TERMINATING|NON_TERMINATING|REWRITE)|primTrustMe|--cubical' ./*.agda; then
    printf 'agda: forbidden construct above\n' >&2
    exit 1
fi

# The interface files are build artefacts; a stale one can mask a broken module.
rm -f ./*.agdai

printf 'agda: %s registered modules, 0 postulates, 0 holes\n' "$count"
