import ZiskFv.AirsClean.ArithDiv.Spec
import Clean.Circuit.Basic

/-!
# ArithDiv circuit operations

The 20 constraints on the Arith AIR's DIV view:

  * 9 boolean flag constraints (na, nb, nr, np, sext, m32, div,
    main_div, main_mul).
  * 3 sign-product witness pins (constraints 6, 7, 8 —
    arith.pil:58-60): `fab`, `na_fb`, `nb_fa`.
  * 8 chunk-level carry equations (constraints 31-38 —
    arith.pil:205-209): the 4-limb packed-product / division
    relation with signed-flag dispatch.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  -- 9 boolean flag constraints (unchanged from A8 partial port).
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.main_div * (1 - row.flags.main_div))
  assertZero (row.flags.main_mul * (1 - row.flags.main_mul))
  -- 3 sign-product witness pins (constraints 6, 7, 8 — arith.pil:58-60).
  assertZero (row.aux.fab
              - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
                  + 4 * row.flags.na * row.flags.nb))
  assertZero (row.aux.na_fb - row.flags.na * (1 - 2 * row.flags.nb))
  assertZero (row.aux.nb_fa - row.flags.nb * (1 - 2 * row.flags.na))
  -- 8 chunk equations (constraints 31-38 — arith.pil:205-209).
  -- 31: (eq[0]) - carry[0] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_0 * row.chunks.b_0
              - row.chunks.c_0
              + 2 * row.flags.np * row.chunks.c_0
              + row.flags.div * row.chunks.d_0
              - 2 * row.flags.nr * row.chunks.d_0
              - row.aux.carry_0 * 65536)
  -- 32: (eq[1]) + carry[0] - carry[1] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_1 * row.chunks.b_0
              + row.aux.fab * row.chunks.a_0 * row.chunks.b_1
              - row.chunks.c_1
              + 2 * row.flags.np * row.chunks.c_1
              + row.flags.div * row.chunks.d_1
              - 2 * row.flags.nr * row.chunks.d_1
              + row.aux.carry_0
              - row.aux.carry_1 * 65536)
  -- 33: (eq[2]) + carry[1] - carry[2] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_2 * row.chunks.b_0
              + row.aux.fab * row.chunks.a_1 * row.chunks.b_1
              + row.aux.fab * row.chunks.a_0 * row.chunks.b_2
              + row.chunks.a_0 * row.aux.nb_fa * row.flags.m32
              + row.chunks.b_0 * row.aux.na_fb * row.flags.m32
              - row.chunks.c_2
              + 2 * row.flags.np * row.chunks.c_2
              + row.flags.div * row.chunks.d_2
              - 2 * row.flags.nr * row.chunks.d_2
              - row.flags.np * row.flags.div * row.flags.m32
              + row.flags.nr * row.flags.m32
              + row.aux.carry_1
              - row.aux.carry_2 * 65536)
  -- 34: (eq[3]) + carry[2] - carry[3] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_0
              + row.aux.fab * row.chunks.a_2 * row.chunks.b_1
              + row.aux.fab * row.chunks.a_1 * row.chunks.b_2
              + row.aux.fab * row.chunks.a_0 * row.chunks.b_3
              + row.chunks.a_1 * row.aux.nb_fa * row.flags.m32
              + row.chunks.b_1 * row.aux.na_fb * row.flags.m32
              - row.chunks.c_3
              + 2 * row.flags.np * row.chunks.c_3
              + row.flags.div * row.chunks.d_3
              - 2 * row.flags.nr * row.chunks.d_3
              + row.aux.carry_2
              - row.aux.carry_3 * 65536)
  -- 35: (eq[4]) + carry[3] - carry[4] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_1
              + row.aux.fab * row.chunks.a_2 * row.chunks.b_2
              + row.aux.fab * row.chunks.a_1 * row.chunks.b_3
              + row.flags.na * row.flags.nb * row.flags.m32
              + row.chunks.b_0 * row.aux.na_fb * (1 - row.flags.m32)
              + row.chunks.a_0 * row.aux.nb_fa * (1 - row.flags.m32)
              - row.flags.np * row.flags.m32 * (1 - row.flags.div)
              - row.flags.np * (1 - row.flags.m32) * row.flags.div
              + row.flags.nr * (1 - row.flags.m32)
              - row.chunks.d_0 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_0 * (1 - row.flags.div)
              + row.aux.carry_3
              - row.aux.carry_4 * 65536)
  -- 36: (eq[5]) + carry[4] - carry[5] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_2
              + row.aux.fab * row.chunks.a_2 * row.chunks.b_3
              + row.chunks.a_1 * row.aux.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_1 * row.aux.na_fb * (1 - row.flags.m32)
              - row.chunks.d_1 * (1 - row.flags.div)
              + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
              + row.aux.carry_4
              - row.aux.carry_5 * 65536)
  -- 37: (eq[6]) + carry[5] - carry[6] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_3
              + row.chunks.a_2 * row.aux.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_2 * row.aux.na_fb * (1 - row.flags.m32)
              - row.chunks.d_2 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
              + row.aux.carry_5
              - row.aux.carry_6 * 65536)
  -- 38: (eq[7]) + carry[6] = 0
  assertZero (65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
              + row.chunks.a_3 * row.aux.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_3 * row.aux.na_fb * (1 - row.flags.m32)
              - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
              - row.chunks.d_3 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
              + row.aux.carry_6)

end ZiskFv.AirsClean.ArithDiv
