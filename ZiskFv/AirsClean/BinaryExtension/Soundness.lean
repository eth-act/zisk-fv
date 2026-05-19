import ZiskFv.AirsClean.BinaryExtension.Spec
import Mathlib.Tactic.LinearCombination

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

theorem soundness (row : BinaryExtensionRow FGL)
    (_h_assumptions : Assumptions row)
    (h_op_is_shift : row.flags.op_is_shift * (1 - row.flags.op_is_shift) = 0)
    (h_b_0 : row.flags.b_0 * (1 - row.flags.b_0) = 0)
    (h_b_1 : row.flags.b_1 * (1 - row.flags.b_1) = 0) :
    Spec row := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h_op_is_shift
  · linear_combination h_b_0
  · linear_combination h_b_1

end ZiskFv.AirsClean.BinaryExtension
