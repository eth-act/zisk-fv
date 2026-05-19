import ZiskFv.AirsClean.Binary.Spec
import Mathlib.Tactic.LinearCombination

namespace ZiskFv.AirsClean.Binary

open Goldilocks

theorem soundness (row : BinaryRow FGL)
    (_h_assumptions : Assumptions row)
    (h_mode32 : row.mode.mode32 * (1 - row.mode.mode32) = 0)
    (h_result_is_a : row.mode.result_is_a * (1 - row.mode.result_is_a) = 0)
    (h_use_first_byte : row.mode.use_first_byte * (1 - row.mode.use_first_byte) = 0)
    (h_c_is_signed : row.mode.c_is_signed * (1 - row.mode.c_is_signed) = 0)
    (h_m32_cs : row.mode.mode32_and_c_is_signed * (1 - row.mode.mode32_and_c_is_signed) = 0) :
    Spec row := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h_mode32
  · linear_combination h_result_is_a
  · linear_combination h_use_first_byte
  · linear_combination h_c_is_signed
  · linear_combination h_m32_cs

end ZiskFv.AirsClean.Binary
