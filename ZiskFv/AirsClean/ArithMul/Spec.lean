import ZiskFv.AirsClean.ArithMul.Row

/-!
# ArithMul Spec + Assumptions (boolean-flag invariants only)

ArithMul's per-row content covers 4-limb carry-chain algebra
(`a * b = c + 2^64 * d` with signed/sign-extension flag variants).
That algebra is captured by the existing
`ZiskFv/Airs/Arith/Mul.lean` Valid_ArithMul record; lifting it into
the Clean Component layer is follow-up work.

The Spec below captures the boolean invariants on the flag columns
(`na`, `nb`, `nr`, `np`, `sext`, `m32`, `div`, `main_div`, `main_mul`)
that are constructively true on every valid Arith row.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

def Assumptions (row : ArithMulRow FGL) : Prop :=
  row.flags.na.val < 2 ∧ row.flags.nb.val < 2 ∧ row.flags.nr.val < 2
  ∧ row.flags.np.val < 2 ∧ row.flags.sext.val < 2 ∧ row.flags.m32.val < 2
  ∧ row.flags.div.val < 2 ∧ row.flags.main_div.val < 2 ∧ row.flags.main_mul.val < 2

def Spec (row : ArithMulRow FGL) : Prop :=
  row.flags.na * (1 - row.flags.na) = 0
  ∧ row.flags.nb * (1 - row.flags.nb) = 0
  ∧ row.flags.nr * (1 - row.flags.nr) = 0
  ∧ row.flags.np * (1 - row.flags.np) = 0
  ∧ row.flags.sext * (1 - row.flags.sext) = 0
  ∧ row.flags.m32 * (1 - row.flags.m32) = 0
  ∧ row.flags.div * (1 - row.flags.div) = 0
  ∧ row.flags.main_div * (1 - row.flags.main_div) = 0
  ∧ row.flags.main_mul * (1 - row.flags.main_mul) = 0

end ZiskFv.AirsClean.ArithMul
