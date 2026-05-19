import ZiskFv.AirsClean.Mem.Spec

/-!
# Mem Soundness

The Spec is the conjunction of the 6 F-typed constraints. Each
constraint is its own Spec clause, so Soundness is structural.

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
    (h_wr_implies_sel : row.wr * (1 - row.sel) = 0) :
    Spec row :=
  ⟨h_sel_dual_bool, h_sel_implies_sel_dual, h_sel_bool,
   h_addr_changes_bool, h_wr_bool, h_wr_implies_sel⟩

end ZiskFv.AirsClean.Mem
