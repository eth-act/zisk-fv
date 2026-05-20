import ZiskFv.AirsClean.ArithMul.Spec
import Clean.Circuit.Basic

/-!
# ArithMul circuit operations (Phase A7.1 — full)

The 9 boolean flag constraints on the Arith AIR's MUL view plus the
11 carry-chain constraints (constraints 6/7/8 + 31..38 from the
extraction layer). Mirrors each `assertZero` call to a
`constraint_N_every_row` body in
`build/extraction/Extraction/Arith.lean`, with `Circuit.main … (column := N)`
substituted by the corresponding named accessor on the `ArithMulRow`.

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
  -- 9 boolean flag constraints.
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.main_div * (1 - row.flags.main_div))
  assertZero (row.flags.main_mul * (1 - row.flags.main_mul))
  -- Constraint 6: fab − ((1 − 2·na) − 2·nb + 4·na·nb) = 0.
  assertZero (row.carries.fab
    - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
       + 4 * row.flags.na * row.flags.nb))
  -- Constraint 7: na_fb − na·(1 − 2·nb) = 0.
  assertZero (row.carries.na_fb - row.flags.na * (1 - 2 * row.flags.nb))
  -- Constraint 8: nb_fa − nb·(1 − 2·na) = 0.
  assertZero (row.carries.nb_fa - row.flags.nb * (1 - 2 * row.flags.na))
  -- Constraint 31.
  assertZero (row.carries.fab * row.chunks.a_0 * row.chunks.b_0
              - row.chunks.c_0
              + 2 * row.flags.np * row.chunks.c_0
              + row.flags.div * row.chunks.d_0
              - 2 * row.flags.nr * row.chunks.d_0
              - row.carries.carry_0 * 65536)
  -- Constraint 32.
  assertZero (row.carries.fab * row.chunks.a_1 * row.chunks.b_0
              + row.carries.fab * row.chunks.a_0 * row.chunks.b_1
              - row.chunks.c_1
              + 2 * row.flags.np * row.chunks.c_1
              + row.flags.div * row.chunks.d_1
              - 2 * row.flags.nr * row.chunks.d_1
              + row.carries.carry_0
              - row.carries.carry_1 * 65536)
  -- Constraint 33.
  assertZero (row.carries.fab * row.chunks.a_2 * row.chunks.b_0
              + row.carries.fab * row.chunks.a_1 * row.chunks.b_1
              + row.carries.fab * row.chunks.a_0 * row.chunks.b_2
              + row.chunks.a_0 * row.carries.nb_fa * row.flags.m32
              + row.chunks.b_0 * row.carries.na_fb * row.flags.m32
              - row.chunks.c_2
              + 2 * row.flags.np * row.chunks.c_2
              + row.flags.div * row.chunks.d_2
              - 2 * row.flags.nr * row.chunks.d_2
              - row.flags.np * row.flags.div * row.flags.m32
              + row.flags.nr * row.flags.m32
              + row.carries.carry_1
              - row.carries.carry_2 * 65536)
  -- Constraint 34.
  assertZero (row.carries.fab * row.chunks.a_3 * row.chunks.b_0
              + row.carries.fab * row.chunks.a_2 * row.chunks.b_1
              + row.carries.fab * row.chunks.a_1 * row.chunks.b_2
              + row.carries.fab * row.chunks.a_0 * row.chunks.b_3
              + row.chunks.a_1 * row.carries.nb_fa * row.flags.m32
              + row.chunks.b_1 * row.carries.na_fb * row.flags.m32
              - row.chunks.c_3
              + 2 * row.flags.np * row.chunks.c_3
              + row.flags.div * row.chunks.d_3
              - 2 * row.flags.nr * row.chunks.d_3
              + row.carries.carry_2
              - row.carries.carry_3 * 65536)
  -- Constraint 35.
  assertZero (row.carries.fab * row.chunks.a_3 * row.chunks.b_1
              + row.carries.fab * row.chunks.a_2 * row.chunks.b_2
              + row.carries.fab * row.chunks.a_1 * row.chunks.b_3
              + row.flags.na * row.flags.nb * row.flags.m32
              + row.chunks.b_0 * row.carries.na_fb * (1 - row.flags.m32)
              + row.chunks.a_0 * row.carries.nb_fa * (1 - row.flags.m32)
              - row.flags.np * row.flags.m32 * (1 - row.flags.div)
              - row.flags.np * (1 - row.flags.m32) * row.flags.div
              + row.flags.nr * (1 - row.flags.m32)
              - row.chunks.d_0 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_0 * (1 - row.flags.div)
              + row.carries.carry_3
              - row.carries.carry_4 * 65536)
  -- Constraint 36.
  assertZero (row.carries.fab * row.chunks.a_3 * row.chunks.b_2
              + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
              + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
              + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
              - row.chunks.d_1 * (1 - row.flags.div)
              + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
              + row.carries.carry_4
              - row.carries.carry_5 * 65536)
  -- Constraint 37.
  assertZero (row.carries.fab * row.chunks.a_3 * row.chunks.b_3
              + row.chunks.a_2 * row.carries.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_2 * row.carries.na_fb * (1 - row.flags.m32)
              - row.chunks.d_2 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
              + row.carries.carry_5
              - row.carries.carry_6 * 65536)
  -- Constraint 38.
  assertZero (65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
              + row.chunks.a_3 * row.carries.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_3 * row.carries.na_fb * (1 - row.flags.m32)
              - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
              - row.chunks.d_3 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
              + row.carries.carry_6)

end ZiskFv.AirsClean.ArithMul
