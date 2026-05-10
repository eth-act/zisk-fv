#!/usr/bin/env bash
# check-no-output-eq-v2.sh — V2: type-walk over canonical theorem
# parameter binders, fail on forbidden Name references after
# reducible-transparency unfolding.
#
# This is the semantic counterpart of V1's `check-no-output-eq.sh`
# (regex over source text). V2 closes the `abbrev` / `@[reducible] def`
# aliasing dodge that V1 cannot see.
#
# Requires `lake build` (consumes oleans). The trust gate's semantic
# checks split is in `check-all-semantic.sh`.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

forbidden=trust/forbidden-types.txt
if [ ! -f "$forbidden" ]; then
  echo "trust-gate (V2): missing $forbidden."
  exit 1
fi

exec lake exe trust-gate check-no-output-eq-v2 "$forbidden"
