import ZiskFv.AirsClean.MemAlign.Row

/-!
# MemAlign Spec + Assumptions

MemAlign has 25 F-typed constraints covering memory-alignment
multiplexers and the register-byte chain. This Spec captures:

* 12 boolean invariants on selectors / write / reset
  (`sel_0..7`, `wr`, `reset`, `sel_up_to_down`, `sel_down_to_up`)
* `boot_pc_zero`: `preL1 * pc = 0`
* `sel_prove_disjoint`: `sel_prove * (sel_up_to_down + sel_down_to_up) = 0`

**Out of scope for this Phase A4 commit** (tracked as A4.1 follow-up):

* `value_0_reconstruction`, `value_1_reconstruction` — 9-term selector
  multiplexers over `reg_0..7`. Verbose but mechanical to add.
* `delta_addr_definition` — references `addr (row - 1)`; cross-row.
* 8 `down_to_up_continuity_N` — cross-row register-chain.

Cross-row constraints live in a separate `cross_row_continuity_at`
adjacency predicate in `Bridge.lean`. The per-row Spec below is what
the Clean `Air.Flat.Component`'s constraint-emitting `main` captures.

## Constructibility audit

Each per-row Spec clause maps 1:1 to a constraint in
`build/extraction/Extraction/MemAlign.lean`:
- Boolean clauses ↔ `constraint_{16,17,...}_every_row` (booleans)
- `boot_pc_zero` ↔ `constraint_{?}_every_row` (preL1 * pc = 0)
- `sel_prove_disjoint` ↔ `constraint_{?}_every_row`

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

/-- Per-row Spec: 14 clauses covering boolean invariants + boot_pc_zero
    + sel_prove_disjoint. -/
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

end ZiskFv.AirsClean.MemAlign
