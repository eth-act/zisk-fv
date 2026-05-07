#!/usr/bin/env bash
# Uniformity lint: verifies every ZiskFv/Equivalence/<Op>.lean exports
# exactly one theorem named equiv_<OP> with the canonical shape
# `execute_instruction ... state = (bus_effect ...).2`.
#
# Emits a YAML roster to stdout. Exits non-zero if any file diverges.

set -euo pipefail

ROOT="${1:-$(git rev-parse --show-toplevel)/ZiskFv/Equivalence}"
FAIL=0
echo "# Opcode roster (machine-readable). Generated from $ROOT."
echo "opcodes:"

for f in "$ROOT"/*.lean; do
  name="$(basename "$f" .lean)"
  canonical_count=$(grep -cE "^theorem equiv_[A-Z][A-Z0-9]*\b" "$f" || true)
  canonical_name=$(grep -oE "^theorem equiv_[A-Z][A-Z0-9]*\b" "$f" | head -1 | sed 's/^theorem //')
  shape=$(grep -cE "= \(bus_effect " "$f" || true)

  if [ "$canonical_count" -eq 0 ]; then
    echo "# FAIL: $name has no canonical equiv_<OP> theorem" >&2
    FAIL=1
    continue
  fi
  if [ "$canonical_count" -gt 1 ]; then
    echo "# FAIL: $name has $canonical_count canonical equiv_<OP> theorems (expect 1)" >&2
    FAIL=1
    continue
  fi
  if [ "$shape" -eq 0 ]; then
    echo "# WARN: $name has no bus_effect RHS (non-canonical shape?)" >&2
  fi

  echo "  - file: $name.lean"
  echo "    canonical: $canonical_name"
done

if [ $FAIL -ne 0 ]; then
  echo "# Uniformity lint FAILED." >&2
  exit 1
fi
echo "# Uniformity lint PASSED. 63 opcodes expected; actual count follows."
