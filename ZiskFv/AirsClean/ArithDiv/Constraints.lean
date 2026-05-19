import ZiskFv.AirsClean.ArithDiv.Spec
import Clean.Circuit.Basic

/-!
# ArithDiv circuit operations (Phase A8 partial)

The 9 boolean flag constraints on the Arith AIR's DIV view (na, nb,
nr, np, sext, m32, div, main_div, main_mul).

**Deferred to Phase A8.1**: the 11 carry-chain constraints for the
4-limb division relation + signed-flag dispatch. Parallel to A7
ArithMul's deferred work.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.main_div * (1 - row.flags.main_div))
  assertZero (row.flags.main_mul * (1 - row.flags.main_mul))

end ZiskFv.AirsClean.ArithDiv
