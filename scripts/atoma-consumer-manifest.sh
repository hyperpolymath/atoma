#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Both real consumers are mandatory, exactly once, before any expensive work.
set -euo pipefail
[[ $# == 1 ]] || exit 2
declare -A seen=()
while read -r repo revision helper oracle extra || [[ -n ${repo:-} ]]; do
    [[ $repo == \#* || -z $repo ]] && continue
    case "$repo" in proven|unified-api-adapter) ;; *) echo 'Invalid consumer manifest: unknown repository' >&2; exit 1 ;; esac
    [[ -z ${seen[$repo]:-} ]] || { echo 'Invalid consumer manifest: duplicate repository' >&2; exit 1; }
    [[ -z ${extra:-} && $revision =~ ^[0-9a-f]{40}$ && -n $helper && -n $oracle ]] || {
        echo 'Invalid consumer manifest: malformed row' >&2; exit 1;
    }
    seen[$repo]=1
done < "$1"
[[ ${seen[proven]:-} == 1 && ${seen[unified-api-adapter]:-} == 1 && ${#seen[@]} == 2 ]] || {
    echo 'Invalid consumer manifest: both Proven and UAA are required' >&2; exit 1;
}
