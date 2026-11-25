#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Bounded CI provisioning deviation; see docs/decisions/ATOMA-TOOLCHAIN.adoc.
set -euo pipefail
: "${RUNNER_TEMP:?GitHub runner scratch directory required}"
: "${GITHUB_PATH:?GitHub PATH file required}"
task="$RUNNER_TEMP/atoma-toolchain"
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
mkdir -p "$task"
cd "$task"
sudo apt-get update
sudo apt-get install -y --no-install-recommends agda-bin=2.6.3-1build1 chezscheme build-essential libgmp-dev curl ca-certificates unzip xz-utils
bash "$root/scripts/atoma-download-zig.sh" "$task"
curl --proto '=https' --proto-redir '=https' -fL --retry 3 https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip -o z3.zip
echo '32c7377026733c9d7b33c21cd77a68f50ba682367207b031a6bfd80140a8722f  z3.zip' | sha256sum -c -
unzip -q z3.zip
echo "$task/z3-4.13.3-x64-glibc-2.35/bin" >> "$GITHUB_PATH"
git init Idris2
git -C Idris2 remote add origin https://github.com/idris-lang/Idris2.git
git -C Idris2 fetch --depth 1 origin b6cbc25d5cd2ef2a250556266fd7b68dfc360f8b
git -C Idris2 checkout --detach FETCH_HEAD
[[ $(git -C Idris2 rev-parse HEAD) == b6cbc25d5cd2ef2a250556266fd7b68dfc360f8b ]]
make -C Idris2 bootstrap SCHEME=scheme PREFIX="$task/idris2" -j2
make -C Idris2 install PREFIX="$task/idris2"
[[ $("$task/idris2/bin/idris2" --version) == 'Idris 2, version 0.8.0-b6cbc25d5' ]]
echo "$task/idris2/bin" >> "$GITHUB_PATH"
dpkg-query -W agda-bin chezscheme libgmp-dev
