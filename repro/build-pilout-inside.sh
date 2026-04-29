#!/bin/bash
# Runs inside the zisk-fv-pilout:repro container.
# Mirrors zisk/tools/test-env/build_setup.sh lines 71-80 — the
# generative-pilout step only, no proving setup.
set -euo pipefail
cd /zisk

echo "▶ Generating fixed data (3 cargo bins)..."
cargo run --release --bin arith_frops_fixed_gen
cargo run --release --bin binary_basic_frops_fixed_gen
cargo run --release --bin binary_extension_frops_fixed_gen

echo "▶ Compiling ZisK PIL → pilout..."
node --max-old-space-size=16384 \
  /opt/pil2-compiler/src/pil.js pil/zisk.pil \
  -I pil,/opt/pil2-proofman/pil2-components/lib/std/pil,state-machines,precompiles \
  -o /output/zisk.pilout \
  -u /tmp/fixed -O fixed-to-file

echo "▶ Hashing output..."
sha256sum /output/zisk.pilout | tee /output/zisk.pilout.sha256
ls -la /output/zisk.pilout
