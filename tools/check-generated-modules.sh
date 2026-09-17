#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
generated_dir="$repo_root/build/extraction/Extraction"

# This is deliberately a closed inventory. Deriving the targets only from the
# current directory would let a generator regression delete a module and shrink
# the compilation check along with it.
expected_modules=(
  Arith
  ArithTable
  Binary
  BinaryAdd
  BinaryExtension
  Buses
  Circuit
  Components/BinaryAdd/Constraints
  Components/BinaryAdd/Manifest
  Components/BinaryAdd/Row
  LookupWiring
  Main
  Mem
  MemAlign
  MemAlignByte
  MemAlignReadByte
  MemAlignRom
  MemAlignWriteByte
  MemGeneratedArtifact
  MemGeneratedConstraintBridge
  MemoryBuses
)

if [[ ! -d "$generated_dir" ]]; then
  echo "generated module directory is missing: $generated_dir" >&2
  echo "run nix run .#populate first" >&2
  exit 1
fi

mapfile -t actual_modules < <(
  find "$generated_dir" -type f -name '*.lean' -printf '%P\n' |
    sed 's/\.lean$//' | sort
)
mapfile -t sorted_expected < <(printf '%s\n' "${expected_modules[@]}" | sort)

if ! diff -u \
    <(printf '%s\n' "${sorted_expected[@]}") \
    <(printf '%s\n' "${actual_modules[@]}"); then
  echo "generated Lean module inventory changed; update the generator or this reviewed inventory" >&2
  exit 1
fi

compile_targets=()
for module in "${expected_modules[@]}"; do
  compile_targets+=("Extraction.${module//\//.}")
done

cd "$repo_root"
lake build "${compile_targets[@]}"

echo "compiled ${#compile_targets[@]} generated Lean modules"
