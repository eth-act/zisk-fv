import ZiskFv.AirsClean.Mem.Row

/-!
# Mem Spec + Assumptions

The Mem AIR's 9 per-row F-typed constraints (`ZiskFv/Airs/Mem.lean:128-174`):

1. `sel_dual * (1 - sel_dual) = 0` (sel_dual boolean)
2. `(1 - sel) * sel_dual = 0`     (sel_dual ⇒ sel)
3. `sel * (1 - sel) = 0`          (sel boolean)
4. `addr_changes * (1 - addr_changes) = 0` (addr_changes boolean)
5. `wr * (1 - wr) = 0`            (wr boolean)
6. `wr * (1 - sel) = 0`           (wr ⇒ sel)
7. `read_same_addr - (1 - addr_changes) * (1 - wr) = 0`
   (read_same_addr definitional identity)
8. `(addr_changes * (1 - wr)) * value_0 = 0`
   (address change without write zeros low value chunk)
9. `(addr_changes * (1 - wr)) * value_1 = 0`
   (address change without write zeros high value chunk)

These per-row F-side invariants are what the AIR's per-row constraints
locally enforce. Cross-row memory consistency (addr/value chronological
agreement) requires the ExtF-side memory-bus permutation, which is
handled by the memory-bus permutation soundness axiom in
`ZiskFv/Airs/MemoryBus/MemBridge.lean` — not part of the per-row Spec
here.

## Constructibility audit

Each Spec clause maps 1:1 to a constraint in
`build/extraction/Extraction/Mem.lean`:
- Clause 1 ↔ `constraint_3_every_row`
- Clause 2 ↔ `constraint_4_every_row`
- Clause 3 ↔ `constraint_5_every_row`
- Clause 4 ↔ `constraint_6_every_row`
- Clause 5 ↔ `constraint_7_every_row`
- Clause 6 ↔ `constraint_8_every_row`
- Clause 7 ↔ `constraint_18_every_row`
- Clause 8 ↔ `constraint_21_every_row`
- Clause 9 ↔ `constraint_23_every_row`

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

def Assumptions (row : MemRow FGL) : Prop :=
  row.sel.val < 2 ∧ row.sel_dual.val < 2
  ∧ row.addr_changes.val < 2 ∧ row.wr.val < 2

/-- Per-row Spec: the 9 extracted PIL F-typed constraints + 2 byte-pack
    packing equations tying the 8 byte-lane witnesses (`x0..x7`) to the
    extracted chunk columns (`value_0`, `value_1`). Byte ranges
    (`xi.val < 256`) flow from `range_bus_sound` and are not part of
    the per-row polynomial Spec. -/
def Spec (row : MemRow FGL) : Prop :=
  row.sel_dual * (1 - row.sel_dual) = 0
  ∧ (1 - row.sel) * row.sel_dual = 0
  ∧ row.sel * (1 - row.sel) = 0
  ∧ row.addr_changes * (1 - row.addr_changes) = 0
  ∧ row.wr * (1 - row.wr) = 0
  ∧ row.wr * (1 - row.sel) = 0
  ∧ row.read_same_addr - (1 - row.addr_changes) * (1 - row.wr) = 0
  ∧ (row.addr_changes * (1 - row.wr)) * row.value_0 = 0
  ∧ (row.addr_changes * (1 - row.wr)) * row.value_1 = 0
  ∧ row.value_0 - (row.x0 + row.x1 * 256 + row.x2 * 65536 + row.x3 * 16777216) = 0
  ∧ row.value_1 - (row.x4 + row.x5 * 256 + row.x6 * 65536 + row.x7 * 16777216) = 0

end ZiskFv.AirsClean.Mem
