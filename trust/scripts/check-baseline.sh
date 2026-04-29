#!/usr/bin/env bash
# check-baseline.sh — fail if `trust/baseline-axioms.txt` is stale
# relative to the live tree.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

BASELINE=trust/baseline-axioms.txt
TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT

# regenerate.py accepts an optional output-path argument.
python3 trust/scripts/regenerate.py "$TMP" >/dev/null

if ! diff -u "$BASELINE" "$TMP" > /tmp/trust-baseline.diff 2>&1; then
  echo "trust-gate: trust/baseline-axioms.txt is OUT OF DATE."
  echo "  Diff (committed -> regenerated):"
  echo
  cat /tmp/trust-baseline.diff
  echo
  echo "  How to fix (legitimate trust change):"
  echo "    trust/scripts/regenerate.sh"
  echo "    git add trust/baseline-axioms.txt"
  echo "  ...then ensure the diff is intentional and reviewed."
  exit 1
fi
echo "trust-gate: baseline-axioms.txt matches live tree."
