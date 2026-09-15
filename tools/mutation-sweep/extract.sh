#!/usr/bin/env bash
# Re-extract Lean from a (possibly mutated) pilout + zisk source tree.
# Mirrors nix/extracted-lean.nix exactly; only the inputs are swapped.
set -euo pipefail
PILOUT="$1"; ZISK="$2"; OUT="$3"
PE=/home/cody/zisk-fv/tools/pil-extract/target/release/pil-extract
mkdir -p "$OUT"

$PE circuit-shim --output "$OUT/Circuit.lean"

for air in Mem MemAlign MemAlignByte MemAlignReadByte MemAlignWriteByte \
           Binary BinaryExtension BinaryAdd; do
  $PE air --pilout "$PILOUT" --air "$air" --skip-unsupported --output "$OUT/$air.lean"
done

$PE air --pilout "$PILOUT" --air Main  --skip-unsupported --output "$OUT/Main.lean"
$PE air --pilout "$PILOUT" --air Arith --skip-unsupported --output "$OUT/Arith.lean"

$PE bus-emissions --pilout "$PILOUT" \
  --airs Main,Arith,Binary,BinaryAdd,BinaryExtension --bus-id 5000 \
  --output "$OUT/Buses.lean"

$PE bus-emissions --pilout "$PILOUT" \
  --airs Main,MemAlign,MemAlignByte,MemAlignReadByte,MemAlignWriteByte --bus-id 10 \
  --output "$OUT/MemoryBuses.lean"

$PE arith-table \
  --rust-source "$ZISK/state-machines/arith/src/arith_table_data.rs" \
  --output "$OUT/ArithTable.lean"

$PE mem-align-rom \
  --pil-source "$ZISK/state-machines/mem/pil/mem_align_rom.pil" \
  --rust-source "$ZISK/state-machines/mem/src/mem_align_rom_sm.rs" \
  --output "$OUT/MemAlignRom.lean"

$PE mem-air-facts --pilout "$PILOUT" --air Mem \
  --pil-source "$ZISK/state-machines/mem/pil/mem.pil" \
  --mem-align-pil-source "$ZISK/state-machines/mem/pil/mem_align.pil" \
  --output "$OUT/../MemAirFacts.md"

$PE mem-generated-artifact --pilout "$PILOUT" --air Mem \
  --output "$OUT/MemGeneratedArtifact.lean"

$PE mem-generated-constraint-bridge --output "$OUT/MemGeneratedConstraintBridge.lean"

$PE lookup-wiring --pilout "$PILOUT" --output "$OUT/LookupWiring.lean"
