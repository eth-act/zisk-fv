import ZiskFv.AirsClean.MemAlign.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlign Soundness

Boolean-invariant clauses follow by `linear_combination` from each
booleanity constraint. The deeper memory-alignment semantics
(byte-shift correctness across 25 F-typed constraints, register
chain) are captured by `Valid_MemAlign`'s record constraints; the
follow-up port will lift that into a richer Clean Component Spec.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

theorem soundness (row : MemAlignRow FGL)
    (_h_assumptions : Assumptions row)
    (h_bool_wr : row.wr * (1 - row.wr) = 0)
    (h_bool_reset : row.reset * (1 - row.reset) = 0)
    (h_bool_sutd : row.sel_up_to_down * (1 - row.sel_up_to_down) = 0)
    (h_bool_sdtu : row.sel_down_to_up * (1 - row.sel_down_to_up) = 0)
    (h_bool_sel0 : row.sel_0 * (1 - row.sel_0) = 0)
    (h_bool_sel1 : row.sel_1 * (1 - row.sel_1) = 0) :
    Spec row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h_bool_wr
  · linear_combination h_bool_reset
  · linear_combination h_bool_sutd
  · linear_combination h_bool_sdtu
  · linear_combination h_bool_sel0
  · linear_combination h_bool_sel1

end ZiskFv.AirsClean.MemAlign
