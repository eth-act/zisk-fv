import ZiskFv.AirsClean.Binary.Spec
import Mathlib.Tactic.LinearCombination

/-!
# Binary Soundness

The 7 F-typed per-row constraints map 1:1 to Spec clauses.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks

theorem soundness (row : BinaryRow FGL)
    (_h_assumptions : Assumptions row)
    (h_mode32 : row.mode.mode32 * (1 - row.mode.mode32) = 0)
    (h_carry_7 : row.chain.carry_7 * (1 - row.chain.carry_7) = 0)
    (h_result_is_a : row.mode.result_is_a * (1 - row.mode.result_is_a) = 0)
    (h_use_first_byte : row.mode.use_first_byte * (1 - row.mode.use_first_byte) = 0)
    (h_c_is_signed : row.mode.c_is_signed * (1 - row.mode.c_is_signed) = 0)
    (h_b_op_or_sext :
      row.chain.b_op_or_sext
        - (row.mode.mode32 * (row.mode.c_is_signed + 512 - row.chain.b_op)
           + row.chain.b_op) = 0)
    (h_m32_cs :
      row.mode.mode32_and_c_is_signed - row.mode.mode32 * row.mode.c_is_signed = 0) :
    Spec row :=
  ⟨h_mode32, h_carry_7, h_result_is_a, h_use_first_byte, h_c_is_signed,
   h_b_op_or_sext, h_m32_cs⟩

end ZiskFv.AirsClean.Binary
