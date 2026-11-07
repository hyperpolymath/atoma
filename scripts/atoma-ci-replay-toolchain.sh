#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Bounded CI bootstrap profile, alongside ATOMA-TOOLCHAIN.adoc.
set -euo pipefail
: "${RUNNER_TEMP:?runner scratch directory required}"
: "${GITHUB_PATH:?GitHub PATH file required}"
task="$RUNNER_TEMP/atoma-replay-toolchain"
mkdir -p "$task"
sudo apt-get update
sudo apt-get install -y --no-install-recommends coq=8.18.0+dfsg-1build2 jq libssl-dev pkg-config
rustup toolchain install 1.99.0 --profile minimal
git init "$task/echidna"
git -C "$task/echidna" remote add origin https://github.com/hyperpolymath/echidna.git
git -C "$task/echidna" fetch --depth 1 origin 2ab7574ae1e574b0e881422fde6252bf79dea178
git -C "$task/echidna" checkout --detach FETCH_HEAD
[[ $(git -C "$task/echidna" rev-parse HEAD) == 2ab7574ae1e574b0e881422fde6252bf79dea178 ]]
(
    cd "$task/echidna"
    cargo +1.99.0 build --locked --release --bin echidna -j 2
)
echo "$task/echidna/target/release" >> "$GITHUB_PATH"
dpkg-query -W coq
"$task/echidna/target/release/echidna" --version
