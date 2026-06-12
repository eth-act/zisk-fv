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

reject_false_probe() {
  if lake env lean trust/consistency/probe_false.lean; then
    echo "probe_false.lean unexpectedly typechecked; project axioms still prove False."
    return 1
  fi
}

run_witnesses() {
  local ok=0
  for f in trust/consistency/completeness_witness_*.lean; do
    [ -e "$f" ] || continue
    lake env lean "$f" || ok=1
  done
  return $ok
}

run "1/6 axiom-deps baseline (V2)"        "$dir/check-axiom-deps.sh"
run "2/6 forbidden types (V2)"            "$dir/check-no-output-eq-v2.sh"
run "3/6 closure vs baseline-axioms (V2)" "$dir/check-closure-vs-baseline.sh"
run "4/6 consistency false probe rejected" reject_false_probe
run "5/6 Sail memory timeline witness" \
  lake env lean trust/consistency/load_byte_agreement_witness.lean
run "6/6 Clean completeness witnesses" run_witnesses

if [ $overall -eq 0 ]; then
  echo "trust-gate (V2 semantic): ALL CHECKS PASSED."
else
  echo "trust-gate (V2 semantic): ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
