import ZiskFv.AirsClean.ArithDiv.Row

/-!
# ArithDiv Spec + Assumptions (boolean-flag invariants only)

Parallel to `ArithMul.Spec`. The dividend/divisor/quotient carry
algebra (`a = b * c + d` with signed-flag variants) lives in
`ZiskFv/Airs/Arith/Div.lean`. The Spec below covers only the
boolean flag invariants.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

def Assumptions (row : ArithDivRow FGL) : Prop :=
  row.flags.na.val < 2 ∧ row.flags.nb.val < 2 ∧ row.flags.nr.val < 2
  ∧ row.flags.np.val < 2 ∧ row.flags.sext.val < 2 ∧ row.flags.m32.val < 2
  ∧ row.flags.div.val < 2 ∧ row.flags.main_div.val < 2 ∧ row.flags.main_mul.val < 2

def Spec (row : ArithDivRow FGL) : Prop :=
  row.flags.na * (1 - row.flags.na) = 0
  ∧ row.flags.nb * (1 - row.flags.nb) = 0
  ∧ row.flags.nr * (1 - row.flags.nr) = 0
  ∧ row.flags.np * (1 - row.flags.np) = 0
  ∧ row.flags.sext * (1 - row.flags.sext) = 0
  ∧ row.flags.m32 * (1 - row.flags.m32) = 0
  ∧ row.flags.div * (1 - row.flags.div) = 0
  ∧ row.flags.main_div * (1 - row.flags.main_div) = 0
  ∧ row.flags.main_mul * (1 - row.flags.main_mul) = 0

end ZiskFv.AirsClean.ArithDiv
