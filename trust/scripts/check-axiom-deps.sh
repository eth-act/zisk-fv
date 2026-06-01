#!/usr/bin/env bash
# check-axiom-deps.sh — V2: per-theorem transitive axiom-closure baseline.
#
# Re-computes each canonical `equiv_<OP>` theorem's transitive non-kernel
# axiom dependencies via `Lean.collectAxioms`, then `diff`s the result
# against `trust/generated/baseline-equiv-axiom-deps.txt`. Catches silent growth
# (or shrinkage) of any single theorem's trust footprint — V1's
# whole-tree baseline-axioms.txt cannot see this.
#
# Requires `lake build` to have run (consumes oleans). The trust gate's
# semantic checks split is in `check-all-semantic.sh`.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-equiv-axiom-deps.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  echo "  Run: lake exe trust-gate regenerate-deps > $baseline"
  echo "  Then review and commit the file."
  exit 1
fi

exec lake exe trust-gate check-deps "$baseline"
