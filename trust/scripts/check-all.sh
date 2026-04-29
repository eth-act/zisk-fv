#!/usr/bin/env bash
# check-all.sh — run every check the trust gate enforces. Used by CI.
# Exit code is the OR of the individual checks (so all failures are
# reported in a single run, not just the first).
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

run "1/4 locality"             "$dir/check-locality.sh"
run "2/4 baseline freshness"   "$dir/check-baseline.sh"
run "3/4 forbidden param shapes" "$dir/check-no-output-eq.sh"
run "4/4 floors + cross-witness" "$dir/check-floor.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate: ALL CHECKS PASSED."
else
  echo "trust-gate: ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
