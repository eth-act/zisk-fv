import ZiskFv.AirsClean.ArithDiv.Spec
import Mathlib.Tactic.LinearCombination

/-!
# ArithDiv Soundness (Clean form)

Proves the 20-clause Spec from the 20 constraint hypotheses
declared in `Constraints.lean`. Each clause maps 1:1 to the
corresponding constraint via `linear_combination`.

## Trust note

No axioms added.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

theorem soundness (row : ArithDivRow FGL)
    (_h_assumptions : Assumptions row)
    -- 9 boolean flag constraints
    (h_na : row.flags.na * (1 - row.flags.na) = 0)
    (h_nb : row.flags.nb * (1 - row.flags.nb) = 0)
    (h_nr : row.flags.nr * (1 - row.flags.nr) = 0)
    (h_np : row.flags.np * (1 - row.flags.np) = 0)
    (h_sext : row.flags.sext * (1 - row.flags.sext) = 0)
    (h_m32 : row.flags.m32 * (1 - row.flags.m32) = 0)
    (h_div : row.flags.div * (1 - row.flags.div) = 0)
    (h_main_div : row.flags.main_div * (1 - row.flags.main_div) = 0)
    (h_main_mul : row.flags.main_mul * (1 - row.flags.main_mul) = 0)
    -- 3 sign-product witness pins (constraints 6, 7, 8)
    (h_c6 : row.aux.fab
              - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
                  + 4 * row.flags.na * row.flags.nb) = 0)
    (h_c7 : row.aux.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0)
    (h_c8 : row.aux.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0)
    -- 8 chunk equations (constraints 31-38)
    (h_c31 :
      row.aux.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.aux.carry_0 * 65536 = 0)
    (h_c32 :
      row.aux.fab * row.chunks.a_1 * row.chunks.b_0
        + row.aux.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.aux.carry_0
        - row.aux.carry_1 * 65536 = 0)
    (h_c33 :
      row.aux.fab * row.chunks.a_2 * row.chunks.b_0
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
        - row.aux.carry_2 * 65536 = 0)
    (h_c34 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_0
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
        - row.aux.carry_3 * 65536 = 0)
    (h_c35 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_1
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
        - row.aux.carry_4 * 65536 = 0)
    (h_c36 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_2
        + row.aux.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.a_1 * row.aux.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_1 * row.aux.na_fb * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.aux.carry_4
        - row.aux.carry_5 * 65536 = 0)
    (h_c37 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.aux.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.aux.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.aux.carry_5
        - row.aux.carry_6 * 65536 = 0)
    (h_c38 :
      65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.aux.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.aux.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.aux.carry_6 = 0) :
    Spec row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h_na
  · linear_combination h_nb
  · linear_combination h_nr
  · linear_combination h_np
  · linear_combination h_sext
  · linear_combination h_m32
  · linear_combination h_div
  · linear_combination h_main_div
  · linear_combination h_main_mul
  · linear_combination h_c6
  · linear_combination h_c7
  · linear_combination h_c8
  · linear_combination h_c31
  · linear_combination h_c32
  · linear_combination h_c33
  · linear_combination h_c34
  · linear_combination h_c35
  · linear_combination h_c36
  · linear_combination h_c37
  · linear_combination h_c38

end ZiskFv.AirsClean.ArithDiv
