#!/usr/bin/env bash
# check-strong-export-closure.sh — V2: assert that the strengthened trace-level
# export theorem
#
#   ZiskFv.Compliance.zisk_compliant_of_accepted_trace_strong
#
# has the EXACT ZiskFv.* project-axiom closure committed in
# trust/generated/baseline-strong-export-closure.txt (expected: empty — 0
# ZiskFv.* axioms, identical to the old global theorem). Mirrors
# check-closure-vs-baseline.sh for the new public theorem so its trust footprint
# cannot drift silently (additions OR removals fail).
#
# Requires `lake build` to have run (consumes oleans).
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-strong-export-closure.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  exit 1
fi

exec lake exe trust-gate check-strong-export-closure "$baseline"
