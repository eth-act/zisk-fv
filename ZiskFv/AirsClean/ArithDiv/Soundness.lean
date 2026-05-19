import ZiskFv.AirsClean.ArithDiv.Spec
import Mathlib.Tactic.LinearCombination

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

theorem soundness (row : ArithDivRow FGL)
    (_h_assumptions : Assumptions row)
    (h_na : row.flags.na * (1 - row.flags.na) = 0)
    (h_nb : row.flags.nb * (1 - row.flags.nb) = 0)
    (h_nr : row.flags.nr * (1 - row.flags.nr) = 0)
    (h_np : row.flags.np * (1 - row.flags.np) = 0)
    (h_sext : row.flags.sext * (1 - row.flags.sext) = 0)
    (h_m32 : row.flags.m32 * (1 - row.flags.m32) = 0)
    (h_div : row.flags.div * (1 - row.flags.div) = 0)
    (h_main_div : row.flags.main_div * (1 - row.flags.main_div) = 0)
    (h_main_mul : row.flags.main_mul * (1 - row.flags.main_mul) = 0) :
    Spec row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h_na
  · linear_combination h_nb
  · linear_combination h_nr
  · linear_combination h_np
  · linear_combination h_sext
  · linear_combination h_m32
  · linear_combination h_div
  · linear_combination h_main_div
  · linear_combination h_main_mul

end ZiskFv.AirsClean.ArithDiv
