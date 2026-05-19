import ZiskFv.AirsClean.MemAlign.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlign Soundness (per-row partial: 14 clauses)

Each Spec clause is 1:1 with its constraint hypothesis; the proof is
structural.

The 11 remaining per-row clauses (value_0/1 reconstruction) and 9
cross-row clauses (delta_addr + down_to_up_continuity_0..7) are
deferred to Phase A4.1.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

theorem soundness (row : MemAlignRow FGL)
    (_h_assumptions : Assumptions row)
    (h_wr : row.wr * (1 - row.wr) = 0)
    (h_reset : row.reset * (1 - row.reset) = 0)
    (h_sutd : row.sel_up_to_down * (1 - row.sel_up_to_down) = 0)
    (h_sdtu : row.sel_down_to_up * (1 - row.sel_down_to_up) = 0)
    (h_sel0 : row.sel_0 * (1 - row.sel_0) = 0)
    (h_sel1 : row.sel_1 * (1 - row.sel_1) = 0)
    (h_sel2 : row.sel_2 * (1 - row.sel_2) = 0)
    (h_sel3 : row.sel_3 * (1 - row.sel_3) = 0)
    (h_sel4 : row.sel_4 * (1 - row.sel_4) = 0)
    (h_sel5 : row.sel_5 * (1 - row.sel_5) = 0)
    (h_sel6 : row.sel_6 * (1 - row.sel_6) = 0)
    (h_sel7 : row.sel_7 * (1 - row.sel_7) = 0)
    (h_boot_pc_zero : row.preL1 * row.pc = 0)
    (h_sel_prove_disjoint :
      row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up) = 0) :
    Spec row :=
  ⟨h_wr, h_reset, h_sutd, h_sdtu,
   h_sel0, h_sel1, h_sel2, h_sel3, h_sel4, h_sel5, h_sel6, h_sel7,
   h_boot_pc_zero, h_sel_prove_disjoint⟩

end ZiskFv.AirsClean.MemAlign
