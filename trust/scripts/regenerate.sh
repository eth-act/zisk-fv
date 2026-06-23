#!/usr/bin/env bash
# Refresh the trust baseline files. Run this after a legitimate
# trust-surface change, commit the updated baseline files alongside.
#
# Eight baselines:
#   trust/generated/baseline-axioms.txt                  — V1: source-text-hash per axiom
#   trust/generated/baseline-equiv-axiom-deps.txt        — V2: per-theorem axiom closure
#   trust/generated/baseline-zisk-riscv-compliant.txt    — V2: uber-theorem project-axiom closure
#   trust/generated/baseline-global-theorem-binders.txt  — V2: uber-theorem binder list
#   trust/generated/baseline-construction-theorem-binders.txt — V2: DEEP (recursive) construction binder leaves
#   trust/generated/baseline-hypothesis-count.txt        — anti-laundering: per-theorem binder counts
#   trust/generated/baseline-caller-burden.txt           — anti-laundering: per-binder ledger (canonical)
#   trust/generated/baseline-wrapper-caller-burden.txt   — anti-laundering: per-binder ledger (wrappers)
#
# The V2 baseline requires `lake build` to have run (consumes oleans);
# we skip it gracefully if the build artefact isn't present. The
# anti-laundering baselines are textual — no build needed.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

python3 trust/scripts/regenerate.py

echo "Refreshing hypothesis-count baseline..."
python3 trust/scripts/count-hypotheses.py > trust/generated/baseline-hypothesis-count.txt
echo "  → trust/generated/baseline-hypothesis-count.txt"

echo "Refreshing caller-burden baseline..."
python3 trust/scripts/regenerate-caller-burden.py > trust/generated/baseline-caller-burden.txt
echo "  → trust/generated/baseline-caller-burden.txt"

echo "Refreshing wrapper caller-burden baseline..."
python3 trust/scripts/regenerate-wrapper-caller-burden.py > trust/generated/baseline-wrapper-caller-burden.txt
echo "  → trust/generated/baseline-wrapper-caller-burden.txt"

echo "Refreshing trust-ledger axiom index..."
python3 tools/trust-ledger-index.py > trust/generated/axiom-index.md
echo "  → trust/generated/axiom-index.md"

if [ -d .lake/build ]; then
  echo "Refreshing V2 per-theorem axiom-dep baseline..."
  lake exe trust-gate regenerate-deps > trust/generated/baseline-equiv-axiom-deps.txt
  echo "  → trust/generated/baseline-equiv-axiom-deps.txt"

  echo "Refreshing global theorem binder baseline..."
  lake exe trust-gate print-global-binders > trust/generated/baseline-global-theorem-binders.txt
  echo "  → trust/generated/baseline-global-theorem-binders.txt"

  echo "Refreshing strong-export theorem binder baseline..."
  lake exe trust-gate print-strong-export-binders > trust/generated/baseline-strong-export-binders.txt
  echo "  → trust/generated/baseline-strong-export-binders.txt"

  echo "Refreshing DEEP construction theorem binder baseline..."
  lake exe trust-gate print-construction-binders-deep > trust/generated/baseline-construction-theorem-binders.txt
  echo "  → trust/generated/baseline-construction-theorem-binders.txt"

  echo "Refreshing uber-theorem axiom-closure baseline..."
  {
    echo "# trust/generated/baseline-zisk-riscv-compliant.txt"
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
    echo "# unqualified axiom names in \`trust/generated/baseline-axioms.txt\`, modulo"
    echo "# the explicit documented non-closure allowlist in"
    echo "# \`trust/tolerated-completeness-axioms.txt\`. The V2 trust gate's"
    echo "# \`check-closure-vs-baseline\` subcommand enforces that relation"
    echo "# mechanically; this file is a standalone audit document — readable"
    echo "# without running Lean."
    echo "#"
    echo "# How this file was generated:"
    echo "#"
    echo "#   lake exe trust-gate print-axiom-closure \\"
    echo "#     ZiskFv.Compliance.zisk_riscv_compliant_program_bus \\"
    echo "#     > trust/generated/baseline-zisk-riscv-compliant.txt"
    echo "#"
    echo "# Refresh via \`trust/scripts/regenerate.sh\` (requires \`lake build\`"
    echo "# artefacts under \`.lake/build/\`). Last regenerated: $(date +%Y-%m-%d)."
    echo "#"
    body=$(lake exe trust-gate print-axiom-closure \
      ZiskFv.Compliance.zisk_riscv_compliant_program_bus)
    if [ -n "$body" ]; then
      n=$(printf '%s\n' "$body" | grep -c .)
    else
      n=0
    fi
    echo "# Total entries: $n"
    echo "#"
    if [ -n "$body" ]; then
      printf '%s\n' "$body"
    fi
  } > trust/generated/baseline-zisk-riscv-compliant.txt
  echo "  → trust/generated/baseline-zisk-riscv-compliant.txt"

  echo "Refreshing strong-export theorem axiom-closure baseline..."
  {
    echo "# trust/generated/baseline-strong-export-closure.txt"
    echo "#"
    echo "# The ZiskFv.* project-axiom closure (transitive ZiskFv.* axioms only — Lean"
    echo "# kernel axioms and Sail-translated module axioms excluded) of the"
    echo "# strengthened trace-level export theorem"
    echo "#"
    echo "#   ZiskFv.Compliance.root_soundness"
    echo "#"
    echo "# This is the #61 channel-balance trace-level export (63/63 RV64IM arms on"
    echo "# the OpEnvelope route). Its project-trust footprint is audited here exactly"
    echo "# as zisk_riscv_compliant_program_bus is audited by"
    echo "# baseline-zisk-riscv-compliant.txt: the V2 gate's check-strong-export-closure"
    echo "# subcommand asserts the live closure equals this file (additions OR removals"
    echo "# fail the gate)."
    echo "#"
    echo "# The closure is EMPTY: this theorem depends on ZERO ZiskFv.* project axioms"
    echo "# (its raw axiom closure is identical to zisk_riscv_compliant_program_bus's —"
    echo "# Lean kernel axioms + Sail-translation axioms only, no sorryAx)."
    echo "#"
    echo "# How this file was generated:"
    echo "#"
    echo "#   lake exe trust-gate print-strong-export-closure \\"
    echo "#     > trust/generated/baseline-strong-export-closure.txt  (body, below the header)"
    echo "#"
    echo "# Refresh via \`trust/scripts/regenerate.sh\` (requires \`lake build\`"
    echo "# artefacts under \`.lake/build/\`). Last regenerated: $(date +%Y-%m-%d)."
    echo "#"
    body=$(lake exe trust-gate print-strong-export-closure)
    if [ -n "$body" ]; then
      n=$(printf '%s\n' "$body" | grep -c .)
    else
      n=0
    fi
    echo "# Total ZiskFv.* axiom entries: $n"
    echo "#"
    if [ -n "$body" ]; then
      printf '%s\n' "$body"
    fi
  } > trust/generated/baseline-strong-export-closure.txt
  echo "  → trust/generated/baseline-strong-export-closure.txt"
else
  echo "Skipping V2 axiom-dep regeneration (no .lake/build/ — run \`lake build\` first)."
  echo "Skipping global theorem binder baseline (no .lake/build/ — run \`lake build\` first)."
  echo "Skipping uber-theorem closure baseline (no .lake/build/ — run \`lake build\` first)."
fi
