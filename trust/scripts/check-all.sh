#!/usr/bin/env bash
# check-all.sh — run every check the trust gate enforces. Used by CI
# and by bin/test.sh. Exit code is the OR of the individual checks
# (so all failures are reported in a single run, not just the first).
set -u
cd "$(git rev-parse --show-toplevel)"

dir="$(dirname "$0")"
overall=0

run() {
  local name=$1; shift
  echo "::: $name :::"
  if ! "$@"; then
    overall=1
  fi
  echo
}

run "1/6 locality"               "$dir/check-locality.sh"
run "2/6 baseline freshness"     "$dir/check-baseline.sh"
run "3/6 forbidden param shapes" "$dir/check-no-output-eq.sh"
run "4/6 floors + cross-witness" "$dir/check-floor.sh"
run "5/6 zero sorry"             "$dir/check-no-sorry.sh"
run "6/6 uniformity (canonical metaplan shape)" "$dir/check-uniformity.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate: ALL CHECKS PASSED."
else
  echo "trust-gate: ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
