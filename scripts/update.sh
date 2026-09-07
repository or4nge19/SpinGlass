#!/usr/bin/env bash
set -euo pipefail

# Update the pinned Mathlib revision and the matching Lean toolchain.
#
# Mathlib is pinned by `rev` in lakefile.toml, so the toolchain must come from *that* revision,
# not from Mathlib master: taking master's `lean-toolchain` would desync the compiler from the
# pinned Mathlib and break the build.

REV="$(sed -n 's/^rev = "\(.*\)"$/\1/p' lakefile.toml | head -1)"
if [ -z "$REV" ]; then
  echo "no 'rev' pin found in lakefile.toml" >&2
  exit 1
fi

echo "Pinned Mathlib revision: $REV"
curl -fsSL "https://raw.githubusercontent.com/leanprover-community/mathlib4/${REV}/lean-toolchain" \
  -o lean-toolchain
lake update
lake exe cache get
