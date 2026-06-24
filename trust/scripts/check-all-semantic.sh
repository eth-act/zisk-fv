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

run_lean_no_sorry() {
  local output status
  output="$(lake env lean "$@" 2>&1)"
  status=$?
  if [ -n "$output" ]; then
    printf '%s\n' "$output"
  fi
  if [ "$status" -ne 0 ]; then
    return "$status"
  fi
  if grep -q 'uses `sorry`' <<<"$output"; then
    echo "Lean file unexpectedly contains sorry: $*"
    return 1
  fi
}

run_witnesses() {
  local ok=0
  for f in trust/consistency/completeness_witness_*.lean; do
    [ -e "$f" ] || continue
    run_lean_no_sorry "$f" || ok=1
  done
  return $ok
}

run "1/13 axiom-deps baseline (V2)"        "$dir/check-axiom-deps.sh"
run "2/13 forbidden types (V2)"            "$dir/check-no-output-eq-v2.sh"
run "3/13 closure vs baseline-axioms (V2)" "$dir/check-closure-vs-baseline.sh"
run "4/13 global theorem binders (V2)"     "$dir/check-global-theorem-binders.sh"
run "5/13 strong-export axiom closure (V2)" "$dir/check-strong-export-closure.sh"
run "6/13 strong-export binders + forbidden types (V2)" "$dir/check-strong-export-binders.sh"
run "7/13 consistency false probe rejected" reject_false_probe
run "8/13 Sail memory timeline witness" \
  run_lean_no_sorry trust/consistency/load_byte_agreement_witness.lean
run "9/13 memory timeline construction witness" \
  run_lean_no_sorry trust/consistency/memory_timeline_construction_witness.lean
run "10/13 memory prefix alignment witness" \
  run_lean_no_sorry trust/consistency/memory_prefix_alignment_witness.lean
run "11/13 global ADD theorem instantiation" \
  run_lean_no_sorry trust/consistency/global_theorem_instantiation_add.lean
run "12/13 global LD theorem instantiation" \
  run_lean_no_sorry trust/consistency/global_theorem_instantiation_ld.lean
run "13/13 Clean completeness witnesses" run_witnesses

if [ $overall -eq 0 ]; then
  echo "trust-gate (V2 semantic): ALL CHECKS PASSED."
else
  echo "trust-gate (V2 semantic): ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
