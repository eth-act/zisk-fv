#!/usr/bin/env bash
# Refresh the trust baseline files. Run this after a legitimate
# trust-surface change, commit the updated baseline files alongside.
#
# Five baselines:
#   trust/baseline-axioms.txt                  — V1: source-text-hash per axiom
#   trust/baseline-equiv-axiom-deps.txt        — V2: per-theorem axiom closure
#   trust/baseline-hypothesis-count.txt        — anti-laundering: per-theorem binder counts
#   trust/baseline-caller-burden.txt           — anti-laundering: per-binder ledger (canonical)
#   trust/baseline-wrapper-caller-burden.txt   — anti-laundering: per-binder ledger (wrappers)
#
# The V2 baseline requires `lake build` to have run (consumes oleans);
# we skip it gracefully if the build artefact isn't present. The
# anti-laundering baselines are textual — no build needed.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

python3 trust/scripts/regenerate.py

echo "Refreshing hypothesis-count baseline..."
python3 trust/scripts/count-hypotheses.py > trust/baseline-hypothesis-count.txt
echo "  → trust/baseline-hypothesis-count.txt"

echo "Refreshing caller-burden baseline..."
python3 trust/scripts/regenerate-caller-burden.py > trust/baseline-caller-burden.txt
echo "  → trust/baseline-caller-burden.txt"

echo "Refreshing wrapper caller-burden baseline..."
python3 trust/scripts/regenerate-wrapper-caller-burden.py > trust/baseline-wrapper-caller-burden.txt
echo "  → trust/baseline-wrapper-caller-burden.txt"

if [ -d .lake/build ]; then
  echo "Refreshing V2 per-theorem axiom-dep baseline..."
  lake exe trust-gate regenerate-deps > trust/baseline-equiv-axiom-deps.txt
  echo "  → trust/baseline-equiv-axiom-deps.txt"
else
  echo "Skipping V2 axiom-dep regeneration (no .lake/build/ — run \`lake build\` first)."
fi
