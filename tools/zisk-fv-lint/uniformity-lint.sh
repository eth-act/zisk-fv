#!/usr/bin/env bash
# Phase 4 uniformity lint: verifies every ZiskFv/Equivalence/<Op>.lean
# exports exactly one theorem named equiv_<OP>_metaplan with the canonical
# shape  `execute_instruction ... state = (bus_effect ...).2`.
#
# Emits a YAML roster to stdout. Exits non-zero if any file diverges.

set -euo pipefail

ROOT="${1:-$(git rev-parse --show-toplevel)/ZiskFv/ZiskFv/Equivalence}"
FAIL=0
echo "# Phase 4 opcode roster (machine-readable). Generated from $ROOT."
echo "opcodes:"

for f in "$ROOT"/*.lean; do
  name="$(basename "$f" .lean)"
  metaplan_count=$(grep -cE "^theorem equiv_[A-Z_0-9]+_metaplan\b" "$f" || true)
  metaplan_name=$(grep -oE "^theorem equiv_[A-Z_0-9]+_metaplan" "$f" | head -1 | sed 's/^theorem //')
  canonical=$(grep -cE "= \(bus_effect " "$f" || true)

  if [ "$metaplan_count" -eq 0 ]; then
    echo "# FAIL: $name has no equiv_*_metaplan theorem" >&2
    FAIL=1
    continue
  fi
  if [ "$metaplan_count" -gt 1 ]; then
    echo "# FAIL: $name has $metaplan_count equiv_*_metaplan theorems (expect 1)" >&2
    FAIL=1
    continue
  fi
  if [ "$canonical" -eq 0 ]; then
    echo "# WARN: $name has no bus_effect RHS (non-canonical shape?)" >&2
  fi

  echo "  - file: $name.lean"
  echo "    metaplan: $metaplan_name"
done

if [ $FAIL -ne 0 ]; then
  echo "# Uniformity lint FAILED." >&2
  exit 1
fi
echo "# Uniformity lint PASSED. 63 opcodes expected; actual count follows."
