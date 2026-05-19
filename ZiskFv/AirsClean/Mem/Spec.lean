import ZiskFv.AirsClean.Mem.Row

/-!
# Mem Spec + Assumptions

The Mem AIR's per-row F-typed constraints are:
- `sel_dual * (1 - sel_dual) = 0` (sel_dual is boolean)
- `(1 - sel) * sel_dual = 0` (sel_dual can only be 1 when sel = 1)
- `sel * (1 - sel) = 0` (sel is boolean)
- `addr_changes * (1 - addr_changes) = 0` (addr_changes is boolean)
- `wr * (1 - wr) = 0` (wr is boolean)
- `wr * (1 - sel) = 0` (writes only on selected rows)

These per-row invariants are what the AIR's F-side constraints
locally enforce. The full memory-consistency Spec (cross-row
agreement on addr/value) requires the ExtF-side bus permutation
that the F-only constraints don't capture; it's covered by the
memory-bus permutation soundness axiom in
`ZiskFv/Airs/MemoryBus/MemBridge.lean`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

def Assumptions (row : MemRow FGL) : Prop :=
  row.sel.val < 2 ∧ row.sel_dual.val < 2
  ∧ row.addr_changes.val < 2 ∧ row.wr.val < 2

/-- Per-row Spec: the 6 boolean invariants on selector / write / dual
    columns hold. -/
def Spec (row : MemRow FGL) : Prop :=
  row.sel_dual * (1 - row.sel_dual) = 0
  ∧ (1 - row.sel) * row.sel_dual = 0
  ∧ row.sel * (1 - row.sel) = 0
  ∧ row.addr_changes * (1 - row.addr_changes) = 0
  ∧ row.wr * (1 - row.wr) = 0
  ∧ row.wr * (1 - row.sel) = 0

end ZiskFv.AirsClean.Mem
