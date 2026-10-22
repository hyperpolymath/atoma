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
# the K axiom. Together they are the Dedukti-CIC subset the specification
# requires for witness export (§6.5).
#
# Exits 0 only if every module checks. Prints one line per module.

set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
AGDA=${AGDA:-agda}

cd "$here/agda"

for m in Bv Lin Core Soundness; do
    if "$AGDA" --safe --without-K "$m.agda" >/dev/null 2>&1; then
        printf 'agda ok   %s\n' "$m"
    else
        printf 'agda FAIL %s\n' "$m" >&2
        "$AGDA" --safe --without-K "$m.agda" 2>&1 | sed -n '2,12p' >&2
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

printf 'agda: 4 modules, 0 postulates, 0 holes\n'
