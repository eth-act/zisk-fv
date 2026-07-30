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

run "1/19 locality"               "$dir/check-locality.sh"
run "2/19 baseline freshness"     "$dir/check-baseline.sh"
run "3/19 active defect-count baseline" "$dir/check-defect-count.sh"
run "4/19 forbidden param shapes" "$dir/check-no-output-eq.sh"
run "5/19 floors + cross-witness" "$dir/check-floor.sh"
run "6/19 zero sorry"             "$dir/check-no-sorry.sh"
run "7/19 uniformity (canonical equivalence shape)" "$dir/check-uniformity.sh"
run "8/19 no new ArithTable opcode axioms" "$dir/check-arith-table-op-axioms.sh"
run "9/19 Clean integration regressions" "$dir/check-clean-integration.sh"
run "10/19 CODEOWNERS trust-boundary coverage" "$dir/check-codeowners.sh"
run "11/19 retired row-shape compatibility shims" "$dir/check-retired-row-shape-shims.sh"
run "12/19 tracked Aeneas extraction artifact policy" "$dir/check-no-checked-in-aeneas-artifacts.sh"
run "13/19 Aeneas generated bridge manifest" "$dir/check-aeneas-generated-bridge-manifest.sh"
run "14/19 Aeneas production-boundary delegation" "$dir/check-aeneas-production-boundary.py"
run "15/19 generated axiom allowlist" "$dir/check-generated-axiom-allowlist.sh"
run "16/19 shrinkage floor (axiom-count monotone)" "$dir/check-shrinkage.sh"
run "17/19 RowData split partition integrity" "$dir/check-rowdata-partition.sh"
run "18/19 module reachability (lake build graph)" "$dir/check-module-reachability.sh"
# One check for every welded AIR, now and in future: AIRs are registered as data
# in `trust/weld-airs.toml`, so adding one never renumbers this list.
run "19/19 weld column maps (all registered AIRs)" "$dir/check-weld-column-maps.py"

if [ $overall -eq 0 ]; then
  echo "trust-gate: ALL CHECKS PASSED."
else
  echo "trust-gate: ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
