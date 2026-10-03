#!/usr/bin/env bash
# Build the official Comparator revision matching lean-toolchain, outside the source tree.
set -euo pipefail
cd "$(dirname "$0")/.."
revision=a4f696825c583ed8a5b4060d9a0faa5b882d365b
location="$PWD/.verification/tools/comparator"
if [ ! -d "$location/.git" ]; then
  mkdir -p "$(dirname "$location")"
  git clone --depth 1 --branch v4.29.0-rc6 https://github.com/leanprover/comparator.git "$location"
fi
if [ "$(git -C "$location" rev-parse HEAD)" != "$revision" ]; then
  echo "Comparator revision mismatch in $location" >&2
  exit 1
fi
if ! cmp -s lean-toolchain "$location/lean-toolchain"; then
  echo "Comparator and project toolchains do not match" >&2
  exit 1
fi
lake -d "$location" build comparator lean4export
printf 'Comparator ready in %s\n' "$location"
