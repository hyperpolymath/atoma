#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# set-repo-metadata.sh — write the GitHub About description and the 20 topics.
#
# Why this is a script and not a one-liner in a chat log: repository metadata is
# part of the project's public description, it has to be reviewable, and it has
# to be reproducible the day someone changes the wording. Committing it means the
# topics are under version control like every other claim this repository makes.
#
# It is NOT run by any gate. It needs a token with `administration: write`
# (`gh auth refresh -s administration`); the CI token this repository usually
# runs under is contents-scoped and gets HTTP 403 here, which is why the metadata
# lives in the tree and is applied deliberately by a maintainer.
#
# Usage:
#   scripts/set-repo-metadata.sh              apply description + topics
#   scripts/set-repo-metadata.sh --dry-run    print the payloads, change nothing
#
# Exit codes: 0 applied (or dry run printed), 1 an API call failed,
#             2 setup error (gh missing, wrong topic count).

set -eu

REPO="${REPO:-hyperpolymath/atoma}"

# Estate style: "Name — what it is. Concrete detail: counts, pipeline, what is
# checked." No claim here that the kernel chain has run — it has not, and the
# description says so.
DESCRIPTION='Atoma — program verification for Zig. Contracts, a subset checker, an Agda-checked soundness theorem for a store-free core, and canonical certificates; COMPLETE status only after Dedukti + Coq/Lean4 kernel checks.'

# 7 topics nearly every hyperpolymath repository carries, then 13 specific to
# Atoma. Order is the order they are written, not a ranking: GitHub sorts them.
TOPICS='
epistemic-computing
epistemic-infrastructure
equivalence-aware-computing
hyperpolymath
open-source
typed-provenance
veridical-computing
formal-verification
program-verification
deductive-verification
proof-certificates
proof-assistants
theorem-proving
smt-solving
zig
agda
idris2
dependent-types
proof-engineering
reproducible-research
'

dry_run=0
case "${1:-}" in
    --dry-run) dry_run=1 ;;
    '') : ;;
    *)
        printf 'usage: %s [--dry-run]\n' "$0" >&2
        exit 2
        ;;
esac

command -v gh >/dev/null 2>&1 || {
    printf 'ERROR: gh is not installed\n' >&2
    exit 2
}

# Validate the topic list against GitHub's rules before spending an API call:
# lowercase ASCII letters, digits and single hyphens, at most 50 characters.
count=0
for t in $TOPICS; do
    count=$((count + 1))
    case "$t" in
        *[!a-z0-9-]*)
            printf 'ERROR: topic %s is not lowercase/digits/hyphen\n' "$t" >&2
            exit 2
            ;;
        --*|*-|*--*)
            printf 'ERROR: topic %s has an illegal hyphen placement\n' "$t" >&2
            exit 2
            ;;
    esac
    [ "${#t}" -le 50 ] || {
        printf 'ERROR: topic %s is longer than 50 characters\n' "$t" >&2
        exit 2
    }
done
[ "$count" -eq 20 ] || {
    printf 'ERROR: expected exactly 20 topics, found %s\n' "$count" >&2
    exit 2
}

# Build the JSON body once, so the dry run and the live run cannot diverge.
topics_json=$(printf '%s\n' $TOPICS | awk 'BEGIN{printf "["} {gsub(/"/,""); printf "%s\"%s\"", (NR>1?",":""), $0} END{print "]"}')

if [ "$dry_run" -eq 1 ]; then
    printf 'repo:        %s\n' "$REPO"
    printf 'description: %s\n' "$DESCRIPTION"
    printf 'description length: %s characters\n' "${#DESCRIPTION}"
    printf 'topics (%s):\n' "$count"
    printf '%s\n' $TOPICS | sed 's/^/  - /'
    printf 'PATCH body:  {"description": %s}\n' "\"$DESCRIPTION\""
    printf 'PUT body:    {"names": %s}\n' "$topics_json"
    exit 0
fi

gh api -X PATCH "repos/$REPO" -f description="$DESCRIPTION" >/dev/null || {
    printf 'ERROR: could not set the description. A 403 here means the token is\n' >&2
    printf '       contents-scoped; refresh it with:\n' >&2
    printf '         gh auth refresh -h github.com -s administration\n' >&2
    exit 1
}
printf 'description set\n'
printf '  %s\n' "$DESCRIPTION"

topics_tmp=$(mktemp)
trap 'rm -f "$topics_tmp"' EXIT INT TERM
printf '{"names": %s}\n' "$topics_json" > "$topics_tmp"

if ! gh api -X PUT "repos/$REPO/topics" \
    -H 'Accept: application/vnd.github+json' --input "$topics_tmp" >/dev/null; then
    printf 'ERROR: could not set the topics (a 403 here has the same cause as\n' >&2
    printf '       the description failure above).\n' >&2
    exit 1
fi
printf '%s topics set\n' "$count"
printf '%s\n' $TOPICS | sed 's/^/  - /'
