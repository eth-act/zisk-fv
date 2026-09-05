#!/usr/bin/env bash
# check-baseline.sh — fail if `trust/generated/baseline-axioms.txt` is stale
# relative to the live tree.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

BASELINE=trust/generated/baseline-axioms.txt
baseline_work=$(mktemp -d)
trap 'rm -rf "$baseline_work"' EXIT

# regenerate.py accepts an optional output-path argument.
python3 trust/scripts/regenerate.py "$baseline_work/current" >/dev/null

if ! diff -u "$BASELINE" "$baseline_work/current" > "$baseline_work/diff" 2>&1; then
  echo "trust-gate: trust/generated/baseline-axioms.txt is OUT OF DATE."
  echo "  Diff (committed -> regenerated):"
  echo
  cat "$baseline_work/diff"
  echo
  echo "  How to fix (legitimate trust change):"
  echo "    trust/scripts/regenerate.sh"
  echo "    git add trust/generated/baseline-axioms.txt"
  echo "  ...then ensure the diff is intentional and reviewed."
  exit 1
fi
echo "trust-gate: baseline-axioms.txt matches live tree."
