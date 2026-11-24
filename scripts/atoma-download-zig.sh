#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Mirrors change availability, never the accepted archive identity.
set -euo pipefail
[[ $# == 1 && $1 == /* ]]
: "${GITHUB_PATH:?GitHub PATH file required}"
mkdir -p "$1"
cd "$1"
archive=zig-x86_64-linux-0.15.2.tar.xz
downloaded=false
for url in \
  "https://zigmirror.hryx.net/zig/$archive" \
  "https://zig.linus.dev/zig/$archive" \
  "https://ziglang.org/download/0.15.2/$archive"; do
    if curl --proto '=https' --proto-redir '=https' --connect-timeout 20 --max-time 120 -fL "$url" -o "$archive"; then
        echo "02aa270f183da276e5b5920b1dac44a63f1a49e55050ebde3aecc9eb82f93239  $archive" | sha256sum -c -
        downloaded=true
        break
    fi
done
[[ $downloaded == true ]] || { echo 'FAIL all pinned Zig download locations unavailable' >&2; exit 1; }
tar -xf "$archive"
echo "$PWD/zig-x86_64-linux-0.15.2" >> "$GITHUB_PATH"
