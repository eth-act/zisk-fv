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

run "1/18 locality"               "$dir/check-locality.sh"
run "2/18 baseline freshness"     "$dir/check-baseline.sh"
run "3/18 forbidden param shapes" "$dir/check-no-output-eq.sh"
run "4/18 floors + cross-witness" "$dir/check-floor.sh"
run "5/18 zero sorry"             "$dir/check-no-sorry.sh"
run "6/18 uniformity (canonical equivalence shape)" "$dir/check-uniformity.sh"
run "7/18 hypothesis-count anti-laundering" "$dir/check-hypothesis-count.sh"
run "8/18 caller-burden ledger (canonical)" "$dir/check-caller-burden.sh"
run "9/18 caller-burden ledger (wrappers)"  "$dir/check-wrapper-caller-burden.sh"
run "10/18 no new ArithTable opcode axioms" "$dir/check-arith-table-op-axioms.sh"
run "11/18 Clean integration regressions" "$dir/check-clean-integration.sh"
run "12/18 CODEOWNERS trust-boundary coverage" "$dir/check-codeowners.sh"
run "13/18 retired row-shape compatibility shims" "$dir/check-retired-row-shape-shims.sh"
run "14/18 tracked Aeneas extraction artifact policy" "$dir/check-no-checked-in-aeneas-artifacts.sh"
run "15/18 Aeneas generated bridge manifest" "$dir/check-aeneas-generated-bridge-manifest.sh"
run "16/18 Aeneas production-boundary delegation" "$dir/check-aeneas-production-boundary.py"
run "17/18 generated axiom allowlist" "$dir/check-generated-axiom-allowlist.sh"
run "18/18 shrinkage floor (axiom-count monotone)" "$dir/check-shrinkage.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate: ALL CHECKS PASSED."
else
  echo "trust-gate: ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
