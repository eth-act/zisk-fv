#!/usr/bin/env bash
# check-no-checked-in-aeneas-artifacts.sh - fail if Aeneas extraction outputs
# are tracked outside the canonical reviewed artifact.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

canonical='trust/aeneas/ProductionM2.lean'

if [[ ! -f "$canonical" ]]; then
  echo "trust-gate: missing canonical tracked Aeneas extraction: $canonical" >&2
  echo "Regenerate it with AENEAS_UPDATE_TRACKED=1 nix run .#aeneas-production-extract." >&2
  exit 1
fi

if ! git ls-files --error-unmatch "$canonical" >/dev/null 2>&1; then
  echo "trust-gate: canonical Aeneas extraction exists but is not tracked: $canonical" >&2
  echo "Add it to git after regenerating with AENEAS_UPDATE_TRACKED=1 nix run .#aeneas-production-extract." >&2
  exit 1
fi

unexpected="$(
  git ls-files \
    | rg '(^|/)(ProductionM[0-9]*\.lean|GeneratedChecks\.lean|production_m[0-9]*\.llbc|.*\.llbc)$' \
    | rg -v "^${canonical}$" \
    || true
)"

if [[ -n "$unexpected" ]]; then
  echo "$unexpected" >&2
  echo "trust-gate: generated Aeneas extraction artifacts are only allowed at $canonical." >&2
  echo "Do not commit LLBC or temporary generated harness files." >&2
  exit 1
fi

echo "trust-gate: canonical tracked Aeneas extraction policy holds."
