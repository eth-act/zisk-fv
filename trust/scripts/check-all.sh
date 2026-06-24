#!/usr/bin/env bash
# check-all.sh — run every check the trust gate enforces. Used by CI
# and by `nix run .#test`. Exit code is the OR of the individual checks
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

run "1/15 locality"               "$dir/check-locality.sh"
run "2/15 baseline freshness"     "$dir/check-baseline.sh"
run "3/15 forbidden param shapes" "$dir/check-no-output-eq.sh"
run "4/15 floors + cross-witness" "$dir/check-floor.sh"
run "5/15 zero sorry"             "$dir/check-no-sorry.sh"
run "6/15 uniformity (canonical equivalence shape)" "$dir/check-uniformity.sh"
run "7/15 no new ArithTable opcode axioms" "$dir/check-arith-table-op-axioms.sh"
run "8/15 Clean integration regressions" "$dir/check-clean-integration.sh"
run "9/15 CODEOWNERS trust-boundary coverage" "$dir/check-codeowners.sh"
run "10/15 retired row-shape compatibility shims" "$dir/check-retired-row-shape-shims.sh"
run "11/15 tracked Aeneas extraction artifact policy" "$dir/check-no-checked-in-aeneas-artifacts.sh"
run "12/15 Aeneas generated bridge manifest" "$dir/check-aeneas-generated-bridge-manifest.sh"
run "13/15 Aeneas production-boundary delegation" "$dir/check-aeneas-production-boundary.py"
run "14/15 generated axiom allowlist" "$dir/check-generated-axiom-allowlist.sh"
run "15/15 shrinkage floor (axiom-count monotone)" "$dir/check-shrinkage.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate: ALL CHECKS PASSED."
else
  echo "trust-gate: ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
