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

run "1/16 locality"               "$dir/check-locality.sh"
run "2/16 baseline freshness"     "$dir/check-baseline.sh"
run "3/16 forbidden param shapes" "$dir/check-no-output-eq.sh"
run "4/16 floors + cross-witness" "$dir/check-floor.sh"
run "5/16 zero sorry"             "$dir/check-no-sorry.sh"
run "6/16 uniformity (canonical equivalence shape)" "$dir/check-uniformity.sh"
run "7/16 hypothesis-count anti-laundering" "$dir/check-hypothesis-count.sh"
run "8/16 caller-burden ledger (canonical)" "$dir/check-caller-burden.sh"
run "9/16 caller-burden ledger (wrappers)"  "$dir/check-wrapper-caller-burden.sh"
run "10/16 no new ArithTable opcode axioms" "$dir/check-arith-table-op-axioms.sh"
run "11/16 Clean integration regressions" "$dir/check-clean-integration.sh"
run "12/16 CODEOWNERS trust-boundary coverage" "$dir/check-codeowners.sh"
run "13/16 retired row-shape compatibility shims" "$dir/check-retired-row-shape-shims.sh"
run "14/16 no checked-in Aeneas extraction artifacts" "$dir/check-no-checked-in-aeneas-artifacts.sh"
run "15/16 Aeneas production-boundary delegation" "$dir/check-aeneas-production-boundary.py"
run "16/16 shrinkage floor (axiom-count monotone)" "$dir/check-shrinkage.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate: ALL CHECKS PASSED."
else
  echo "trust-gate: ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
