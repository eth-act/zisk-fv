import ZiskFv.AirsClean.MemAlign.Row

/-!
# MemAlign Spec + Assumptions

MemAlign has 25 F-typed constraints covering memory-alignment
multiplexers and the register-byte chain. This Spec captures the
16 per-row clauses:

* 12 boolean invariants on selectors / write / reset
  (`sel_0..7`, `wr`, `reset`, `sel_up_to_down`, `sel_down_to_up`)
* `boot_pc_zero`: `preL1 * pc = 0`
* `sel_prove_disjoint`: `sel_prove * (sel_up_to_down + sel_down_to_up) = 0`
* `value_0_reconstruction`, `value_1_reconstruction` — 9-term selector
  multiplexers over `reg_0..7`

Cross-row constraints (`delta_addr_definition` + 8
`down_to_up_continuity_N`) live in a separate `cross_row_at`
adjacency predicate in `CrossRow.lean`. The per-row Spec below is
what the Clean `Air.Flat.Component`'s constraint-emitting `main`
captures.

## Constructibility audit

Each per-row Spec clause maps 1:1 to a constraint in
`build/extraction/Extraction/MemAlign.lean`:
- Boolean clauses ↔ `constraint_{17..28}_every_row`
- `boot_pc_zero` ↔ `constraint_16_every_row` (preL1 * pc = 0)
- `sel_prove_disjoint` ↔ `constraint_30_every_row`
- `value_0_reconstruction` ↔ `constraint_31_every_row`
- `value_1_reconstruction` ↔ `constraint_32_every_row`

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

def Assumptions (row : MemAlignRow FGL) : Prop :=
  row.wr.val < 2 ∧ row.reset.val < 2
  ∧ row.sel_up_to_down.val < 2 ∧ row.sel_down_to_up.val < 2
  ∧ row.sel_0.val < 2 ∧ row.sel_1.val < 2 ∧ row.sel_2.val < 2 ∧ row.sel_3.val < 2
  ∧ row.sel_4.val < 2 ∧ row.sel_5.val < 2 ∧ row.sel_6.val < 2 ∧ row.sel_7.val < 2

/-- Per-row Spec: 16 clauses covering boolean invariants + boot_pc_zero
    + sel_prove_disjoint + value_0/1 reconstruction. -/
def Spec (row : MemAlignRow FGL) : Prop :=
  row.wr * (1 - row.wr) = 0
  ∧ row.reset * (1 - row.reset) = 0
  ∧ row.sel_up_to_down * (1 - row.sel_up_to_down) = 0
  ∧ row.sel_down_to_up * (1 - row.sel_down_to_up) = 0
  ∧ row.sel_0 * (1 - row.sel_0) = 0
  ∧ row.sel_1 * (1 - row.sel_1) = 0
  ∧ row.sel_2 * (1 - row.sel_2) = 0
  ∧ row.sel_3 * (1 - row.sel_3) = 0
  ∧ row.sel_4 * (1 - row.sel_4) = 0
  ∧ row.sel_5 * (1 - row.sel_5) = 0
  ∧ row.sel_6 * (1 - row.sel_6) = 0
  ∧ row.sel_7 * (1 - row.sel_7) = 0
  ∧ row.preL1 * row.pc = 0
  ∧ row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up) = 0
  ∧ row.value_0 -
      (row.sel_prove *
        (row.sel_0 * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)
         + row.sel_1 * (row.reg_1 + row.reg_2 * 256 + row.reg_3 * 65536 + row.reg_4 * 16777216)
         + row.sel_2 * (row.reg_2 + row.reg_3 * 256 + row.reg_4 * 65536 + row.reg_5 * 16777216)
         + row.sel_3 * (row.reg_3 + row.reg_4 * 256 + row.reg_5 * 65536 + row.reg_6 * 16777216)
         + row.sel_4 * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)
         + row.sel_5 * (row.reg_5 + row.reg_6 * 256 + row.reg_7 * 65536 + row.reg_0 * 16777216)
         + row.sel_6 * (row.reg_6 + row.reg_7 * 256 + row.reg_0 * 65536 + row.reg_1 * 16777216)
         + row.sel_7 * (row.reg_7 + row.reg_0 * 256 + row.reg_1 * 65536 + row.reg_2 * 16777216))
       + (row.sel_up_to_down + row.sel_down_to_up)
         * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)) = 0
  ∧ row.value_1 -
      (row.sel_prove *
        (row.sel_0 * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)
         + row.sel_1 * (row.reg_5 + row.reg_6 * 256 + row.reg_7 * 65536 + row.reg_0 * 16777216)
         + row.sel_2 * (row.reg_6 + row.reg_7 * 256 + row.reg_0 * 65536 + row.reg_1 * 16777216)
         + row.sel_3 * (row.reg_7 + row.reg_0 * 256 + row.reg_1 * 65536 + row.reg_2 * 16777216)
         + row.sel_4 * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)
         + row.sel_5 * (row.reg_1 + row.reg_2 * 256 + row.reg_3 * 65536 + row.reg_4 * 16777216)
         + row.sel_6 * (row.reg_2 + row.reg_3 * 256 + row.reg_4 * 65536 + row.reg_5 * 16777216)
         + row.sel_7 * (row.reg_3 + row.reg_4 * 256 + row.reg_5 * 65536 + row.reg_6 * 16777216))
       + (row.sel_up_to_down + row.sel_down_to_up)
         * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)) = 0

end ZiskFv.AirsClean.MemAlign
