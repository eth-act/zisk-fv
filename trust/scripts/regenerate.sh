#!/usr/bin/env bash
# Refresh the trust baseline files. Run this after a legitimate
# trust-surface change, commit the updated baseline files alongside.
#
# Two baselines:
#   trust/baseline-axioms.txt              — V1: source-text-hash per axiom
#   trust/baseline-equiv-axiom-deps.txt    — V2: per-theorem axiom closure
#
# The V2 baseline requires `lake build` to have run (consumes oleans);
# we skip it gracefully if the build artefact isn't present.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

python3 trust/scripts/regenerate.py

if [ -d .lake/build ]; then
  echo "Refreshing V2 per-theorem axiom-dep baseline..."
  lake exe trust-gate regenerate-deps > trust/baseline-equiv-axiom-deps.txt
  echo "  → trust/baseline-equiv-axiom-deps.txt"
else
  echo "Skipping V2 axiom-dep regeneration (no .lake/build/ — run \`lake build\` first)."
fi
