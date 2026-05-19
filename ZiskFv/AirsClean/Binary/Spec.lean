import ZiskFv.AirsClean.Binary.Row

/-!
# Binary Spec + Assumptions

The Binary AIR's 7 F-typed per-row constraints
(`ZiskFv/Airs/Binary/Binary.lean`):

1. `mode32 * (1 - mode32) = 0`
2. `carry_7 * (1 - carry_7) = 0` (booleanity of the final carry)
3. `result_is_a * (1 - result_is_a) = 0`
4. `use_first_byte * (1 - use_first_byte) = 0`
5. `c_is_signed * (1 - c_is_signed) = 0`
6. `b_op_or_sext - (mode32 * (c_is_signed + 512 - b_op) + b_op) = 0`
   (b_op_or_sext multiplexer)
7. `mode32_and_c_is_signed - mode32 * c_is_signed = 0`
   (mode32_and_c_is_signed product identity)

Constraints 8–13 (lookup-permutation against `BinaryTable`) are
handled compositionally via the bus model — not per-row F-typed.

## Constructibility audit

Each Spec clause maps 1:1 to a constraint in
`build/extraction/Extraction/Binary.lean`'s
`constraint_0_every_row` through `constraint_6_every_row`.

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
  ∧ row.chain.carry_7.val < 2

/-- Per-row Spec: the 7 F-typed constraints hold. -/
def Spec (row : BinaryRow FGL) : Prop :=
  row.mode.mode32 * (1 - row.mode.mode32) = 0
  ∧ row.chain.carry_7 * (1 - row.chain.carry_7) = 0
  ∧ row.mode.result_is_a * (1 - row.mode.result_is_a) = 0
  ∧ row.mode.use_first_byte * (1 - row.mode.use_first_byte) = 0
  ∧ row.mode.c_is_signed * (1 - row.mode.c_is_signed) = 0
  ∧ row.chain.b_op_or_sext
      - (row.mode.mode32 * (row.mode.c_is_signed + 512 - row.chain.b_op)
         + row.chain.b_op) = 0
  ∧ row.mode.mode32_and_c_is_signed - row.mode.mode32 * row.mode.c_is_signed = 0

end ZiskFv.AirsClean.Binary
