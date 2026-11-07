#!/usr/bin/env bash
# Bounded CI provisioning deviation; see docs/decisions/ATOMA-TOOLCHAIN.adoc.
set -euo pipefail
: "${RUNNER_TEMP:?GitHub runner scratch directory required}"
: "${GITHUB_PATH:?GitHub PATH file required}"
task="$RUNNER_TEMP/atoma-toolchain"
mkdir -p "$task"
cd "$task"
sudo apt-get update
sudo apt-get install -y --no-install-recommends agda-bin=2.6.3-1build1 chezscheme build-essential libgmp-dev curl ca-certificates unzip xz-utils
curl -fL --retry 3 https://ziglang.org/download/0.15.2/zig-x86_64-linux-0.15.2.tar.xz -o zig.tar.xz
echo '02aa270f183da276e5b5920b1dac44a63f1a49e55050ebde3aecc9eb82f93239  zig.tar.xz' | sha256sum -c -
tar -xf zig.tar.xz
echo "$task/zig-x86_64-linux-0.15.2" >> "$GITHUB_PATH"
curl -fL --retry 3 https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip -o z3.zip
echo '32c7377026733c9d7b33c21cd77a68f50ba682367207b031a6bfd80140a8722f  z3.zip' | sha256sum -c -
unzip -q z3.zip
echo "$task/z3-4.13.3-x64-glibc-2.35/bin" >> "$GITHUB_PATH"
git init Idris2
git -C Idris2 remote add origin https://github.com/idris-lang/Idris2.git
git -C Idris2 fetch --depth 1 origin 15a3e4e70843f7a34100f6470c04b791330788df
git -C Idris2 checkout --detach FETCH_HEAD
[[ $(git -C Idris2 rev-parse HEAD) == 15a3e4e70843f7a34100f6470c04b791330788df ]]
make -C Idris2 bootstrap SCHEME=scheme -j2
make -C Idris2 install PREFIX="$task/idris2"
echo "$task/idris2/bin" >> "$GITHUB_PATH"
dpkg-query -W agda-bin chezscheme libgmp-dev
