#!/bin/bash
# Build the ZisK Lean extraction tree.
#
# Pipeline:
#   1. Build (or reuse) build/zisk.pilout via Docker (codygunton/zisk
#      @0bfdc9582 + pil2-compiler v0.8.0 + pil2-proofman v0.15.0).
#   2. Run tools/pil-extract over each AIR to produce
#      ZiskFv/Extraction/*.lean, the auto-generated Lean constraint
#      definitions that the proof package imports.
#
# This is the canonical way to produce the Extraction layer. The
# resulting files are gitignored — the local build IS the source of
# truth, not a checked-in copy. Run once after cloning, and again
# whenever docker/versions.txt changes.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# --- Step 1: ensure the pilout exists ---
if [ ! -f build/zisk.pilout ]; then
    echo "▶ build/zisk.pilout missing — building it (~6 min cold)…"
    docker/build-pilout.sh
fi

# --- Step 2: build the extractor (release for speed) ---
mkdir -p ZiskFv/Extraction
echo "▶ Building tools/pil-extract…"
(cd tools/pil-extract && cargo build --release --quiet)
EXTRACT=tools/pil-extract/target/release/pil-extract

# --- Step 3: extract per-AIR Lean files ---
echo "▶ Extracting AIR constraints to ZiskFv/Extraction/…"

# Full-AIR extractions (no constraint subsetting needed; --skip-unsupported
# emits stubs for FixedCol/Challenge operands the extractor doesn't
# render yet — those constraints are not used by the proofs).
#
# NOTE: ZiskFv/Extraction/ArithTable.lean is hand-transcribed from
# zisk/state-machines/arith/src/arith_table_data.rs (74-row constant
# table that PIL generates separately). It stays checked in and is
# NOT regenerated here. See its header comment for provenance.
for air in Mem MemAlign MemAlignByte MemAlignReadByte MemAlignWriteByte \
           Binary BinaryExtension BinaryAdd; do
    $EXTRACT --pilout build/zisk.pilout --air "$air" --skip-unsupported \
        --output "ZiskFv/Extraction/$air.lean"
done

# Subset extractions: Main and Arith are huge; the proofs only use a
# specific set of constraint indices, and emitting stubs for the rest
# would balloon the file. The --only filters mirror what verify-phase1
# and verify-phase2 used to pass.
$EXTRACT --pilout build/zisk.pilout --air Main \
    --only 8,9,15,16,17,18,19,20,24,30 \
    --output ZiskFv/Extraction/Main.lean

$EXTRACT --pilout build/zisk.pilout --air Arith \
    --only 2,6,7,8,31,32,33,34,35,36,37,38,40,41,42,43,44,45,46 \
    --output ZiskFv/Extraction/Arith.lean

# Bus-emission extraction for the operation bus (id=5000) across the
# 5 AIRs that emit on it. Goes into Buses.lean.
#
# NOTE: ZiskFv/Extraction/MemoryBuses.lean is hand-curated (filtered
# subset of memory-bus emissions with hand-written documentation,
# distinct namespace). It stays checked in like ArithTable.lean.
$EXTRACT --pilout build/zisk.pilout \
    --airs Main,Arith,Binary,BinaryAdd,BinaryExtension \
    --bus-emissions --bus-id 5000 \
    --output ZiskFv/Extraction/Buses.lean

# --- Step 4: report ---
echo
echo "✅ Extraction tree built: $(ls ZiskFv/Extraction/*.lean | wc -l) files"
ls -1 ZiskFv/Extraction/*.lean
