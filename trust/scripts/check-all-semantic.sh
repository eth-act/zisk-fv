#!/usr/bin/env bash
# check-all-semantic.sh — V2 trust-gate semantic checks.
#
# Runs the elaborated-environment checks (per-theorem axiom-closure
# baseline + binder-type forbidden-Names walk). Requires `lake build`
# to have run; consumes oleans.
#
# The V1 syntactic gate (`check-all.sh`) is independent and runs
# without oleans.
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

run "1/3 axiom-deps baseline (V2)"       "$dir/check-axiom-deps.sh"
run "2/3 forbidden types (V2)"           "$dir/check-no-output-eq-v2.sh"
run "3/3 closure vs baseline-axioms (V2)" "$dir/check-closure-vs-baseline.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate (V2 semantic): ALL CHECKS PASSED."
else
  echo "trust-gate (V2 semantic): ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
