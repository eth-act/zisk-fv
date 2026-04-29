#!/usr/bin/env bash
# check-floor.sh — sanity floors. The whole gate collapses if
# regenerate.py or the locality grep silently produces empty output.
# Hard-coded floors catch that.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# Floor 1: total number of axiom/opaque/constant declarations in the
# baseline must be >= MIN_AXIOMS. Catches a sabotaged regenerate.py
# that produces empty output, or an allowlist edited to empty.
MIN_AXIOMS=80
axiom_count=$(grep -cE '^[0-9a-f]{16}  ' trust/baseline-axioms.txt 2>/dev/null || echo 0)
if [ "$axiom_count" -lt "$MIN_AXIOMS" ]; then
  echo "trust-gate: FLOOR FAILURE — only $axiom_count axioms in baseline (expected >= $MIN_AXIOMS)."
  echo "  This can happen if regenerate.py was sabotaged or the allowlist was emptied."
  exit 1
fi

# Floor 2: count `_metaplan_tier1` theorems. Must be >= MIN_TIER1.
# Catches a sweep that accidentally dropped tier1 companions.
MIN_TIER1=40
tier1_count=$(grep -rhE '^[[:space:]]*theorem[[:space:]]+equiv_[A-Z][A-Z0-9_]*_metaplan_tier1' \
              ZiskFv/Equivalence | wc -l)
if [ "$tier1_count" -lt "$MIN_TIER1" ]; then
  echo "trust-gate: FLOOR FAILURE — only $tier1_count tier1 theorems found (expected >= $MIN_TIER1)."
  echo "  This can happen if a sweep accidentally dropped tier1 companions."
  exit 1
fi

# Floor 3: cross-witness. Re-count via the same Python parser used by
# regenerate.py, but applied to the ENTIRE tree (not just allowlisted
# files). Should equal Floor 1's count — if greater, the allowlist
# was edited to exclude a file that still contains trust constructs.
tree_count=$(python3 -c "
import sys
sys.path.insert(0, 'trust/scripts')
from pathlib import Path
import importlib.util
spec = importlib.util.spec_from_file_location('regen', 'trust/scripts/regenerate.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
total = 0
for f in Path('ZiskFv').rglob('*.lean'):
    for _ in m.parse_blocks(f):
        total += 1
print(total)
")
if [ "$tree_count" -ne "$axiom_count" ]; then
  echo "trust-gate: CROSS-WITNESS FAILURE — tree-wide parser found $tree_count"
  echo "  axiom-shaped declarations but baseline tracks only $axiom_count. The"
  echo "  allowlist may have been edited to exclude a file that still contains"
  echo "  trust constructs. Check trust/allowed-axiom-files.txt + check-locality."
  exit 1
fi

echo "trust-gate: floors OK — $axiom_count axioms / $tier1_count tier1 theorems / cross-witness matches."
