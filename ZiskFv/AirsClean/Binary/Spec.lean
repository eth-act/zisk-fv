import ZiskFv.AirsClean.Binary.Row

/-!
# Binary Spec + Assumptions (boolean-mode invariants only)

The full Binary circuit content (8-byte ALU pipeline with carry
chain across `b_op_or_sext = b_op + b_sext`) lives in
`ZiskFv/Airs/Binary/Binary.lean`. The Spec below covers booleanity
invariants on the mode selector columns
(`mode32`, `result_is_a`, `use_first_byte`, `c_is_signed`,
`mode32_and_c_is_signed`).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks

def Assumptions (row : BinaryRow FGL) : Prop :=
  row.mode.mode32.val < 2
  ∧ row.mode.result_is_a.val < 2
  ∧ row.mode.use_first_byte.val < 2
  ∧ row.mode.c_is_signed.val < 2
  ∧ row.mode.mode32_and_c_is_signed.val < 2

def Spec (row : BinaryRow FGL) : Prop :=
  row.mode.mode32 * (1 - row.mode.mode32) = 0
  ∧ row.mode.result_is_a * (1 - row.mode.result_is_a) = 0
  ∧ row.mode.use_first_byte * (1 - row.mode.use_first_byte) = 0
  ∧ row.mode.c_is_signed * (1 - row.mode.c_is_signed) = 0
  ∧ row.mode.mode32_and_c_is_signed * (1 - row.mode.mode32_and_c_is_signed) = 0

end ZiskFv.AirsClean.Binary
