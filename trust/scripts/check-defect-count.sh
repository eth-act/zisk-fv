#!/usr/bin/env bash
# check-defect-count.sh — fail if the explicit DefectId boundary changed
# without deliberately refreshing its reviewed count baseline.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-defect-count.txt
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
python3 trust/scripts/regenerate-defect-count.py > "$tmp"

if ! diff -u "$baseline" "$tmp"; then
  cat <<'EOF'
trust-gate: active defect count is stale.
Refresh it deliberately with:
  python3 trust/scripts/regenerate-defect-count.py > trust/generated/baseline-defect-count.txt
Then review the DefectId and defect-ledger changes together.
EOF
  exit 1
fi

echo "trust-gate: active defect count matches DefectId."
