#!/usr/bin/env bash
# check-floor.sh — sanity floors. The whole gate collapses if
# regenerate.py or the locality grep silently produces empty output.
# Hard-coded floors catch that.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# Floor 1: total number of axiom/opaque/constant declarations in the
# baseline must be >= MIN_AXIOMS. Catches a sabotaged regenerate.py
# that produces empty output, or an allowlist edited to empty.
MIN_AXIOMS=83
axiom_count=$(grep -cE '^[0-9a-f]{16}  ' trust/baseline-axioms.txt 2>/dev/null || echo 0)
if [ "$axiom_count" -lt "$MIN_AXIOMS" ]; then
  echo "trust-gate: FLOOR FAILURE — only $axiom_count axioms in baseline (expected >= $MIN_AXIOMS)."
  echo "  This can happen if regenerate.py was sabotaged or the allowlist was emptied."
  exit 1
fi

# Floor 2: count canonical bare `equiv_<OP>` theorems (no underscore-suffix).
# Must be >= MIN_CANONICAL. The bare equiv_<OP> is the strong form for
# all 63 opcodes — the 7 loads were rewritten to derive their
# cross-entry rd-value equations from circuit witnesses (see
# `ZiskFv/Circuit/LoadDerivation.lean` and the corresponding closure
# axioms in `Airs/MemoryBus/MemBridge.lean` and
# `Airs/BinaryExtensionTable.lean`). Catches a sweep that accidentally
# dropped the canonical strong forms.
MIN_CANONICAL=63
canonical_count=$(grep -rhE '^theorem[[:space:]]+equiv_[A-Z][A-Z0-9]*[[:space:]]*$|^theorem[[:space:]]+equiv_[A-Z][A-Z0-9]*[[:space:]]+\(' \
              ZiskFv/Equivalence | wc -l)
if [ "$canonical_count" -lt "$MIN_CANONICAL" ]; then
  echo "trust-gate: FLOOR FAILURE — only $canonical_count canonical equiv_<OP> theorems found (expected >= $MIN_CANONICAL)."
  echo "  This can happen if a sweep accidentally dropped canonical equivalence theorems."
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

echo "trust-gate: floors OK — $axiom_count axioms / $canonical_count canonical equiv_<OP> theorems / cross-witness matches."
