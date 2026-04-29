#!/bin/bash
# Build the Sail-Lean RV64D model reproducibly via Docker, then
# tree-diff against NethermindEth/sail-riscv-lean @ 81c8c84f
# (the pin Lake resolves to in ZiskFv/lake-manifest.json).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

mkdir -p out/repro/sail-lean
echo "▶ docker build (slow on first run — ~30–60 min, OCaml + Sail + sail-riscv)…"
docker build -t zisk-fv-sail-lean:repro -f repro/Dockerfile.sail-lean repro/

echo "▶ docker run…"
docker run --rm -v "$PWD/out/repro/sail-lean:/output" zisk-fv-sail-lean:repro

echo
echo "▶ Comparing against the Lake-resolved LeanRV @ 81c8c84f…"
LEAN_RV_DIR=ZiskFv/.lake/packages/LeanRV
if [ ! -d "$LEAN_RV_DIR" ]; then
  echo "  Lake hasn't resolved LeanRV yet. Run \`(cd ZiskFv && lake update)\` first."
  exit 1
fi

# Compute manifest hashes for both trees, scoped to the .lean files
# (the deploy step in update-sail-build.yml ships extra README/report.py
# that aren't part of the build output).
hash_tree () {
  (cd "$1" && find . -type f -name '*.lean' ! -path './.lake/*' \
    -print0 | sort -z | xargs -0 sha256sum) | sha256sum | awk '{print $1}'
}
local_hash=$(hash_tree out/repro/sail-lean)
lake_hash=$(hash_tree "$LEAN_RV_DIR")

echo "  reproduced:     $local_hash"
echo "  Lake-resolved:  $lake_hash"
if [ "$local_hash" = "$lake_hash" ]; then
  echo "  ✅ TREE-IDENTICAL (Lean source files)"
else
  echo "  ⚠ DIFFER. Per-file diff:"
  diff -ruq out/repro/sail-lean "$LEAN_RV_DIR" \
    | grep -v '/.lake' | grep -v 'README.md\|report.py\|build_log.txt' \
    | head -30
fi
