import ZiskFv.AirsClean.ArithMul.Spec
import Clean.Circuit.Basic

/-!
# ArithMul circuit operations (Phase A7 partial)

The 9 boolean flag constraints on the Arith AIR's MUL view (na, nb,
nr, np, sext, m32, div, main_div, main_mul).

**Deferred to Phase A7.1**: the 11 carry-chain constraints
(`mul_carry_chain_holds` in `ZiskFv/Airs/Arith/Mul.lean:356-367` —
constraints 6, 7, 8, 31..38 from the extraction layer). Encoding
these as `assertZero` requires translating the 4-limb multiply
relation into `Expression FGL` form (verbose but mechanical).

The lookup against `ArithTable` (which enforces division of mode
flags into the actual MUL/DIV/MULU/etc. operation) is at the
Component-instantiation level, consuming the existing
`arith_table_*` trust-ledger axioms (class #6b).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var ArithMulRow FGL) : Circuit FGL Unit := do
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.main_div * (1 - row.flags.main_div))
  assertZero (row.flags.main_mul * (1 - row.flags.main_mul))

end ZiskFv.AirsClean.ArithMul
