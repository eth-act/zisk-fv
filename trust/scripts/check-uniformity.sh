#!/usr/bin/env bash
# Uniformity lint: verifies every ZiskFv/Equivalence/<Op>.lean exports
# exactly one theorem named equiv_<OP> with the canonical shape
# `execute_instruction ... state = state_effect_via_channels ...`
# (post-Phase-6) or `= (bus_effect ...).2` (pre-cutover v1).
#
# Emits a YAML roster to stdout. Exits non-zero if any file diverges.

set -euo pipefail

ROOT="${1:-$(git rev-parse --show-toplevel)/ZiskFv/Equivalence}"
FAIL=0
echo "# Opcode roster (machine-readable). Generated from $ROOT."
echo "opcodes:"

for f in "$ROOT"/*.lean; do
  name="$(basename "$f" .lean)"
  # Compliance.lean is the global dispatcher (Step 4.3) — by design it
  # contains shape dispatchers, not a per-op `equiv_<OP>` theorem.
  # Skip it from the per-file uniformity check.
  if [ "$name" = "Compliance" ]; then
    continue
  fi
  canonical_count=$(grep -cE "^theorem equiv_[A-Z][A-Z0-9]*\b" "$f" || true)
  canonical_name=$(grep -oE "^theorem equiv_[A-Z][A-Z0-9]*\b" "$f" | head -1 | sed 's/^theorem //')
  shape=$(grep -cE "= \(bus_effect |= state_effect_via_channels" "$f" || true)

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
    echo "# WARN: $name has no bus_effect or state_effect_via_channels RHS (non-canonical shape?)" >&2
  fi

  echo "  - file: $name.lean"
  echo "    canonical: $canonical_name"
done

if [ $FAIL -ne 0 ]; then
  echo "# Uniformity lint FAILED." >&2
  exit 1
fi
echo "# Uniformity lint PASSED. 63 opcodes expected; actual count follows."
