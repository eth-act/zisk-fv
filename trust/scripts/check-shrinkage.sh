#!/usr/bin/env bash
# check-shrinkage.sh — enforce that the axiom count in
# trust/generated/baseline-axioms.txt never exceeds the floor recorded in
# trust/.shrinkage-floor. Lowering the floor requires editing that
# file in the same commit that removes axioms — CODEOWNER review of
# the diff is the audit step.
#
# This gate exists to make the "full Clean integration" migration
# safe against trust regressions: every per-AIR or per-phase PR must
# hold-or-shrink the axiom closure. The V3 closure gate
# (check-closure-vs-baseline) catches per-theorem dependency drift;
# this script catches global axiom-count drift.
set -eu
cd "$(git rev-parse --show-toplevel)"

floor_file="trust/.shrinkage-floor"
baseline_file="trust/generated/baseline-axioms.txt"

if [ ! -f "$floor_file" ]; then
  echo "FAIL: $floor_file is missing"
  exit 1
fi
if [ ! -f "$baseline_file" ]; then
  echo "FAIL: $baseline_file is missing"
  exit 1
fi

floor=$(tr -d '[:space:]' < "$floor_file")
current=$(awk '$3=="axiom" {n++} END {print n+0}' "$baseline_file")

if ! echo "$floor" | grep -Eq '^[0-9]+$'; then
  echo "FAIL: floor '$floor' is not a non-negative integer"
  exit 1
fi

if [ "$current" -gt "$floor" ]; then
  cat <<EOF
FAIL: axiom count exceeds shrinkage floor
  current  : $current  (axioms in $baseline_file)
  floor    : $floor    (recorded in $floor_file)

The Clean-integration plan requires monotone shrinkage. To raise
the floor (i.e. add a new axiom), a CODEOWNER must explicitly
approve editing $floor_file. Otherwise: remove the offending
axiom or land the change in a separate CODEOWNER-reviewed PR.
EOF
  exit 1
fi

echo "OK: $current axioms ≤ floor $floor"
