import ZiskFv.AirsClean.ArithMul.Spec
import Mathlib.Tactic.LinearCombination

/-!
# ArithMul Soundness (Clean form)

Given the 9 boolean flag constraints + the 11 carry-chain constraints
(constraints 6/7/8 + 31..38 from the extraction layer), prove the
matching `Spec` clauses. Each clause is closed by `linear_combination`
against the corresponding hypothesis (they are syntactic
re-expressions in the same ring, so identity coefficients suffice).

## Trust note

No axioms added.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

theorem soundness (row : ArithMulRow FGL)
    (_h_assumptions : Assumptions row)
    -- 9 boolean flag hypotheses.
    (h_na : row.flags.na * (1 - row.flags.na) = 0)
    (h_nb : row.flags.nb * (1 - row.flags.nb) = 0)
    (h_nr : row.flags.nr * (1 - row.flags.nr) = 0)
    (h_np : row.flags.np * (1 - row.flags.np) = 0)
    (h_sext : row.flags.sext * (1 - row.flags.sext) = 0)
    (h_m32 : row.flags.m32 * (1 - row.flags.m32) = 0)
    (h_div : row.flags.div * (1 - row.flags.div) = 0)
    (h_main_div : row.flags.main_div * (1 - row.flags.main_div) = 0)
    (h_main_mul : row.flags.main_mul * (1 - row.flags.main_mul) = 0)
    -- 11 carry-chain hypotheses.
    (h_c6 : row.carries.fab - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
              + 4 * row.flags.na * row.flags.nb) = 0)
    (h_c7 : row.carries.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0)
    (h_c8 : row.carries.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0)
    (h_c31 :
        row.carries.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.carries.carry_0 * 65536 = 0)
    (h_c32 :
        row.carries.fab * row.chunks.a_1 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.carries.carry_0
        - row.carries.carry_1 * 65536 = 0)
    (h_c33 :
        row.carries.fab * row.chunks.a_2 * row.chunks.b_0
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
        - row.carries.carry_2 * 65536 = 0)
    (h_c34 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_0
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
        - row.carries.carry_3 * 65536 = 0)
    (h_c35 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_1
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
        - row.carries.carry_4 * 65536 = 0)
    (h_c36 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.carries.carry_4
        - row.carries.carry_5 * 65536 = 0)
    (h_c37 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.carries.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.carries.carry_5
        - row.carries.carry_6 * 65536 = 0)
    (h_c38 :
        65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.carries.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.carries.carry_6 = 0) :
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

end ZiskFv.AirsClean.ArithMul
