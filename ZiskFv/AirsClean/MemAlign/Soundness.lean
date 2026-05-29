import ZiskFv.AirsClean.MemAlign.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlign Soundness (per-row: 16 clauses)

Each per-row Spec clause is 1:1 with its constraint hypothesis; the
proof is structural.

The cross-row constraints (`delta_addr_definition` + 8
`down_to_up_continuity_N`) live as a separate `cross_row_at`
adjacency predicate in `CrossRow.lean`. They are consumed by
downstream callers directly, not via per-row Soundness.

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
      row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up) = 0)
    (h_value_0 :
      row.value_0 -
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
           * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)) = 0)
    (h_value_1 :
      row.value_1 -
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
           * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)) = 0) :
    Spec row :=
  ⟨h_wr, h_reset, h_sutd, h_sdtu,
   h_sel0, h_sel1, h_sel2, h_sel3, h_sel4, h_sel5, h_sel6, h_sel7,
   h_boot_pc_zero, h_sel_prove_disjoint, h_value_0, h_value_1⟩

end ZiskFv.AirsClean.MemAlign
