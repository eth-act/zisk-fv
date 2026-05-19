import ZiskFv.AirsClean.Mem.Spec

/-!
# Mem Soundness

The 9 F-typed per-row constraints map 1:1 to Spec clauses, so
Soundness is structural — the proof is `⟨h_1, h_2, …, h_9⟩`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

theorem soundness (row : MemRow FGL)
    (_h_assumptions : Assumptions row)
    (h_sel_dual_bool : row.sel_dual * (1 - row.sel_dual) = 0)
    (h_sel_implies_sel_dual : (1 - row.sel) * row.sel_dual = 0)
    (h_sel_bool : row.sel * (1 - row.sel) = 0)
    (h_addr_changes_bool : row.addr_changes * (1 - row.addr_changes) = 0)
    (h_wr_bool : row.wr * (1 - row.wr) = 0)
    (h_wr_implies_sel : row.wr * (1 - row.sel) = 0)
    (h_read_same_addr_def : row.read_same_addr - (1 - row.addr_changes) * (1 - row.wr) = 0)
    (h_addr_change_no_write_value_0 : (row.addr_changes * (1 - row.wr)) * row.value_0 = 0)
    (h_addr_change_no_write_value_1 : (row.addr_changes * (1 - row.wr)) * row.value_1 = 0) :
    Spec row :=
  ⟨h_sel_dual_bool, h_sel_implies_sel_dual, h_sel_bool,
   h_addr_changes_bool, h_wr_bool, h_wr_implies_sel,
   h_read_same_addr_def,
   h_addr_change_no_write_value_0, h_addr_change_no_write_value_1⟩

end ZiskFv.AirsClean.Mem
