#!/usr/bin/env bash
# Wrapper for the Sail-Lean RV64D Docker build. Produces build/sail-lean/
# from the upstream sail/sail-riscv commits pinned in docker/versions.txt
# (via Dockerfile.sail-lean's ARG defaults). After it finishes, verifies
# the produced tree's sha256 matches expected-sail-lean-tree-sha256.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

mkdir -p build/sail-lean

echo "▶ Building Docker image zisk-fv-sail-lean (cached on subsequent runs)…"
docker build -t zisk-fv-sail-lean -f docker/Dockerfile.sail-lean docker/

echo "▶ Running container to generate build/sail-lean/…"
docker run --rm -v "$PWD/build/sail-lean:/output" zisk-fv-sail-lean

expected=$(grep "^expected-sail-lean-tree-sha256" docker/versions.txt | awk -F"= *" '{print $2}')
actual=$( (cd build/sail-lean && find . -type f -name "*.lean" ! -path "./.lake/*" -print0 \
            | sort -z | xargs -0 sha256sum) | sha256sum | awk '{print $1}')
if [ "$expected" = "$actual" ]; then
    echo "▶ Tree hash matches docker/versions.txt: $actual"
else
    echo "❌ Tree hash mismatch — expected $expected, got $actual"
    exit 1
fi
