#!/usr/bin/env bash
# Refresh the trust baseline files. Run this after a legitimate
# trust-surface change, commit the updated baseline files alongside.
#
# Six baselines:
#   trust/baseline-axioms.txt                  — V1: source-text-hash per axiom
#   trust/baseline-equiv-axiom-deps.txt        — V2: per-theorem axiom closure
#   trust/baseline-zisk-riscv-compliant.txt    — V2: uber-theorem project-axiom closure
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

echo "Refreshing trust-ledger axiom index..."
python3 tools/trust-ledger-index.py > trust/axiom-index.md
echo "  → trust/axiom-index.md"

if [ -d .lake/build ]; then
  echo "Refreshing V2 per-theorem axiom-dep baseline..."
  lake exe trust-gate regenerate-deps > trust/baseline-equiv-axiom-deps.txt
  echo "  → trust/baseline-equiv-axiom-deps.txt"

  echo "Refreshing uber-theorem axiom-closure baseline..."
  {
    echo "# trust/baseline-zisk-riscv-compliant.txt"
    echo "#"
    echo "# The project-axiom closure (transitive ZiskFv.* axioms only — Lean kernel"
    echo "# axioms and Sail-translated module axioms excluded) of the global"
    echo "# compliance theorem"
    echo "#"
    echo "#   ZiskFv.Compliance.zisk_riscv_compliant_program_bus"
    echo "#"
    echo "# IS the trusted computing base of zisk-fv. This file is a flat"
    echo "# enumeration of that closure for external auditors who want to inspect"
    echo "# the surface without running Lean."
    echo "#"
    echo "# Source-of-truth cross-check: this set must match the reachable"
    echo "# unqualified axiom names in \`trust/baseline-axioms.txt\`, modulo"
    echo "# the explicit completeness-direction allowlist in"
    echo "# \`trust/tolerated-completeness-axioms.txt\`. The V2 trust gate's"
    echo "# \`check-closure-vs-baseline\` subcommand enforces that relation"
    echo "# mechanically; this file is a standalone audit document — readable"
    echo "# without running Lean."
    echo "#"
    echo "# How this file was generated:"
    echo "#"
    echo "#   lake exe trust-gate print-axiom-closure \\"
    echo "#     ZiskFv.Compliance.zisk_riscv_compliant_program_bus \\"
    echo "#     > trust/baseline-zisk-riscv-compliant.txt"
    echo "#"
    echo "# Refresh via \`trust/scripts/regenerate.sh\` (requires \`lake build\`"
    echo "# artefacts under \`.lake/build/\`). Last regenerated: $(date +%Y-%m-%d)."
    echo "#"
    body=$(lake exe trust-gate print-axiom-closure \
      ZiskFv.Compliance.zisk_riscv_compliant_program_bus)
    n=$(echo "$body" | wc -l)
    echo "# Total entries: $n"
    echo "#"
    echo "$body"
  } > trust/baseline-zisk-riscv-compliant.txt
  echo "  → trust/baseline-zisk-riscv-compliant.txt"
else
  echo "Skipping V2 axiom-dep regeneration (no .lake/build/ — run \`lake build\` first)."
  echo "Skipping uber-theorem closure baseline (no .lake/build/ — run \`lake build\` first)."
fi
