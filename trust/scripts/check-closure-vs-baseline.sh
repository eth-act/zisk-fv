#!/usr/bin/env bash
# check-closure-vs-baseline.sh — V2: assert that the uber-theorem's
# transitive project-axiom closure equals exactly the project axioms
# in `trust/baseline-axioms.txt`.
#
# Catches the kind of drift the per-theorem
# `baseline-equiv-axiom-deps.txt` cannot see — a hash-fresh axiom
# that no theorem actually uses (dead trust). Per-theorem checks
# spot the inverse (an axiom whose closure changed) but cannot
# detect dead ledger entries that aren't on any reachable path.
#
# Requires `lake build` to have run (consumes oleans).
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/baseline-axioms.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  exit 1
fi

exec lake exe trust-gate check-closure-vs-baseline "$baseline"
