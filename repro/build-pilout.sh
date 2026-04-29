#!/bin/bash
# Build pil/zisk.pilout reproducibly via Docker, then verify the
# semantic structure matches the vendored copy.
#
# We compare structurally (AIR list + per-AIR column/constraint
# counts) rather than byte-identically: the protobuf serialization
# embeds source-line-number annotations from pil2-proofman's std/pil
# library, which drift across pil2-proofman patch versions even when
# the pinned tag is the same. zisk-fv's proofs consume AIR structure
# via tools/zisk-pil-extract, never the embedded annotations, so the
# structural fingerprint is the load-bearing reproducibility check.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

mkdir -p out/repro
echo "▶ docker build…"
# Build context is repro/ — the Dockerfile clones ZisK from upstream
# at the pinned commit, so we don't need the parent repo as context.
docker build -t zisk-fv-pilout:repro -f repro/Dockerfile.pilout repro/

echo "▶ docker run…"
docker run --rm -v "$PWD/out/repro:/output" zisk-fv-pilout:repro

echo
echo "▶ Comparing AIR structure (semantic fingerprint)…"
EXTRACT=tools/zisk-pil-extract/target/debug/zisk-pil-extract
if [ ! -x "$EXTRACT" ]; then
  echo "  Building zisk-pil-extract first…"
  (cd tools/zisk-pil-extract && cargo build --quiet)
fi

vendored_fingerprint=$($EXTRACT --pilout pil/zisk.pilout --list | sha256sum | awk '{print $1}')
reproduced_fingerprint=$($EXTRACT --pilout out/repro/zisk.pilout --list | sha256sum | awk '{print $1}')

echo "  vendored AIR fingerprint:    $vendored_fingerprint"
echo "  reproduced AIR fingerprint:  $reproduced_fingerprint"

if [ "$vendored_fingerprint" = "$reproduced_fingerprint" ]; then
  echo "  ✅ STRUCTURALLY IDENTICAL — every AIR (name, columns, constraints) matches."
else
  echo "  ❌ DIFFER. Per-AIR diff:"
  diff <($EXTRACT --pilout pil/zisk.pilout --list) \
       <($EXTRACT --pilout out/repro/zisk.pilout --list)
  exit 1
fi

echo
echo "▶ Note: byte-identical reproduction not yet achieved. Residual"
echo "  delta is in source-line-number annotations from pil2-proofman's"
echo "  std/pil library (consumed for human error messages, not by"
echo "  zisk-fv's proofs)."
echo "  vendored size:    $(stat -c %s pil/zisk.pilout) bytes"
echo "  reproduced size:  $(stat -c %s out/repro/zisk.pilout) bytes"
