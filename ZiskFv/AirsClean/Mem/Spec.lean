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

/-- Per-row Spec: the 9 F-typed constraints hold. -/
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

theorem sel_dual_boolean_of_spec
    (row : MemRow FGL) (h_spec : Spec row) :
    row.sel_dual = 0 ∨ row.sel_dual = 1 := by
  have h := h_spec.1
  rcases mul_eq_zero.mp h with h_zero | h_one_sub
  · exact Or.inl h_zero
  · exact Or.inr (sub_eq_zero.mp h_one_sub).symm

theorem sel_boolean_of_spec
    (row : MemRow FGL) (h_spec : Spec row) :
    row.sel = 0 ∨ row.sel = 1 := by
  have h := h_spec.2.2.1
  rcases mul_eq_zero.mp h with h_zero | h_one_sub
  · exact Or.inl h_zero
  · exact Or.inr (sub_eq_zero.mp h_one_sub).symm

theorem addr_changes_boolean_of_spec
    (row : MemRow FGL) (h_spec : Spec row) :
    row.addr_changes = 0 ∨ row.addr_changes = 1 := by
  have h := h_spec.2.2.2.1
  rcases mul_eq_zero.mp h with h_zero | h_one_sub
  · exact Or.inl h_zero
  · exact Or.inr (sub_eq_zero.mp h_one_sub).symm

theorem wr_boolean_of_spec
    (row : MemRow FGL) (h_spec : Spec row) :
    row.wr = 0 ∨ row.wr = 1 := by
  have h := h_spec.2.2.2.2.1
  rcases mul_eq_zero.mp h with h_zero | h_one_sub
  · exact Or.inl h_zero
  · exact Or.inr (sub_eq_zero.mp h_one_sub).symm

theorem sel_of_sel_dual_one_of_spec
    (row : MemRow FGL) (h_spec : Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    row.sel = 1 := by
  have h := h_spec.2.1
  rw [h_sel_dual] at h
  have h_one_sub : 1 - row.sel = 0 := by simpa using h
  exact (sub_eq_zero.mp h_one_sub).symm

theorem sel_of_wr_one_of_spec
    (row : MemRow FGL) (h_spec : Spec row)
    (h_wr : row.wr = 1) :
    row.sel = 1 := by
  have h := h_spec.2.2.2.2.2.1
  rw [h_wr] at h
  have h_one_sub : 1 - row.sel = 0 := by simpa using h
  exact (sub_eq_zero.mp h_one_sub).symm

theorem read_same_addr_eq_of_spec
    (row : MemRow FGL) (h_spec : Spec row) :
    row.read_same_addr = (1 - row.addr_changes) * (1 - row.wr) := by
  have h := h_spec.2.2.2.2.2.2.1
  linear_combination h

theorem read_addr_change_value_0_zero_of_spec
    (row : MemRow FGL) (h_spec : Spec row)
    (h_addr_changes : row.addr_changes = 1)
    (h_wr : row.wr = 0) :
    row.value_0 = 0 := by
  have h := h_spec.2.2.2.2.2.2.2.1
  rw [h_addr_changes, h_wr] at h
  linear_combination h

theorem read_addr_change_value_1_zero_of_spec
    (row : MemRow FGL) (h_spec : Spec row)
    (h_addr_changes : row.addr_changes = 1)
    (h_wr : row.wr = 0) :
    row.value_1 = 0 := by
  have h := h_spec.2.2.2.2.2.2.2.2
  rw [h_addr_changes, h_wr] at h
  linear_combination h

end ZiskFv.AirsClean.Mem
