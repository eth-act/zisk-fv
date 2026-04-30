#!/usr/bin/env bash
# Wrapper for the pilout Docker build. Produces build/zisk.pilout from
# the upstream sources pinned in docker/versions.txt (via
# Dockerfile.pilout's ARG defaults). Run after a fresh clone, or
# whenever versions.txt changes.
#
# This script is called automatically by docker/build-zisk-lean.sh
# when build/zisk.pilout is missing.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

mkdir -p build

echo "▶ Building Docker image zisk-fv-pilout (cached on subsequent runs)…"
docker build -t zisk-fv-pilout -f docker/Dockerfile.pilout docker/

echo "▶ Running container to generate build/zisk.pilout…"
docker run --rm -v "$PWD/build:/output" zisk-fv-pilout

echo "▶ Done. build/zisk.pilout produced."
ls -la build/zisk.pilout
