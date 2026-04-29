#!/bin/bash
# Build build/zisk.pilout via Docker. The pilout is no longer vendored
# in the repo — this script is the canonical way to produce it. Run
# once after cloning the repo (~6 min cold; the Docker image layer
# caches so subsequent runs are fast). The output persists in build/
# and is consumed by `just verify-phase*`.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

mkdir -p build
echo "▶ docker build (cold: ~5 min cargo + npm + node compile; warm: cached)…"
# Build context is repro/ — the Dockerfile clones ZisK from upstream
# at the pinned commit, so we don't need the parent repo as context.
docker build -t zisk-fv-pilout:repro -f repro/Dockerfile.pilout repro/

echo "▶ docker run (in-container PIL compile, ~6 min)…"
docker run --rm -v "$PWD/build:/output" zisk-fv-pilout:repro

echo
echo "▶ Verifying output…"
if [ ! -f build/zisk.pilout ]; then
  echo "  ❌ build/zisk.pilout was not produced" >&2
  exit 1
fi
sha256sum build/zisk.pilout
echo "  size: $(stat -c %s build/zisk.pilout) bytes"
echo
echo "✅ Pilout built. Continue with: just verify-phase0  (or verify-phase1, …)"
