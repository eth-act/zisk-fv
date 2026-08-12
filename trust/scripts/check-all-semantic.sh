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

run_root_soundness_instantiations() {
  local ok=0
  for f in trust/consistency/root_soundness_instantiation_*.lean; do
    [ -e "$f" ] || continue
    run_lean_no_sorry "$f" || ok=1
  done
  return $ok
}

run_register_mem_bus_witnesses() {
  local ok=0
  for f in trust/consistency/register_mem_bus_*.lean; do
    [ -e "$f" ] || continue
    run_lean_no_sorry "$f" || ok=1
  done
  return $ok
}

run "1/20 axiom-deps baseline (V2)"        "$dir/check-axiom-deps.sh"
run "2/20 forbidden types (V2)"            "$dir/check-no-output-eq-v2.sh"
run "3/20 closure vs baseline-axioms (V2)" "$dir/check-closure-vs-baseline.sh"
run "4/20 global theorem binders (V2)"     "$dir/check-global-theorem-binders.sh"
run "5/20 strong-export axiom closure (V2)" "$dir/check-strong-export-closure.sh"
run "6/20 strong-export binders + forbidden types (V2)" "$dir/check-strong-export-binders.sh"
run "7/20 consistency false probe rejected" reject_false_probe
run "8/20 MemAlign narrow-load lane constraint repro" \
  run_lean_no_sorry trust/consistency/memalign_narrow_load_lane_defect.lean
run "9/20 signed-DIV quotient-sign defect repro" \
  run_lean_no_sorry trust/consistency/arith_div_quotient_sign_defect.lean
run "10/20 Sail memory timeline witness" \
  run_lean_no_sorry trust/consistency/load_byte_agreement_witness.lean
run "11/20 memory timeline construction witness" \
  run_lean_no_sorry trust/consistency/memory_timeline_construction_witness.lean
run "12/20 memory prefix alignment witness" \
  run_lean_no_sorry trust/consistency/memory_prefix_alignment_witness.lean
run "13/20 SD/LD Mem-prefix constructibility" \
  run_lean_no_sorry trust/consistency/memory_prefix_sd_ld_mem_table.lean
run "14/20 global ADD theorem instantiation" \
  run_lean_no_sorry trust/consistency/global_theorem_instantiation_add.lean
run "15/20 global LD theorem instantiation" \
  run_lean_no_sorry trust/consistency/global_theorem_instantiation_ld.lean
run "16/20 root_soundness instantiation witnesses" run_root_soundness_instantiations
run "17/20 Clean completeness witnesses" run_witnesses
run "18/20 register MemBus balance witnesses" run_register_mem_bus_witnesses
run "19/20 register walk acyclicity (#342)" \
  run_lean_no_sorry trust/consistency/register_walk_acyclic.lean
run "20/20 Aeneas extraction-pin raw axiom closure (V2)" \
  "$dir/check-extraction-closure.sh"

if [ $overall -eq 0 ]; then
  echo "trust-gate (V2 semantic): ALL CHECKS PASSED."
else
  echo "trust-gate (V2 semantic): ONE OR MORE CHECKS FAILED. See above."
fi
exit $overall
