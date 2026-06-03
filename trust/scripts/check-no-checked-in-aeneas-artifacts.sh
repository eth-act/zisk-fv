#!/usr/bin/env bash
# check-no-checked-in-aeneas-artifacts.sh - fail if reproducible Aeneas
# extraction outputs are committed instead of regenerated under build/.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

if git ls-files | rg -n \
    '(^|/)(ProductionM[0-9]*\.lean|GeneratedChecks\.lean|production_m[0-9]*\.llbc|.*\.llbc)$'; then
  echo "trust-gate: generated Aeneas extraction artifacts must stay untracked." >&2
  echo "Re-run nix run .#aeneas-production-extract; do not commit generated Lean/LLBC." >&2
  exit 1
fi

echo "trust-gate: no generated Aeneas extraction artifacts are tracked."
