import ZiskFv.AirsClean.ArithDiv.Row

/-!
# ArithDiv Spec + Assumptions

Parallel to `ArithMul.Spec`. The Spec is structured as the original
9 boolean flag invariants plus the 11 carry-chain clauses that
encode the 4-limb divide relation `a = b * c + d` with signed-flag
dispatch (arith.pil:58-60 and arith.pil:205-209).

The 11 carry-chain clauses break down as:

  * 3 sign-product witnesses (constraints 6, 7, 8):
    `fab = 1 - 2na - 2nb + 4*na*nb`,
    `na_fb = na*(1 - 2nb)`, `nb_fa = nb*(1 - 2na)`.
  * 8 chunk-equations (constraints 31-38): the 8 packed-product
    carry equations relating `fab * a[i] * b[j]` cross-terms, the
    signed-flag offsets (`np`, `nr`, `m32`, `div` selectors), the
    `na_fb`/`nb_fa`/`na*nb` summands, the result chunks `c[i]`,
    `d[i]`, and the seven 16-bit carries `carry[0..6]`.

These are precisely the 11 PIL constraints on which
`arith_div_unsigned_packed_correct` /
`arith_div_signed_packed_correct` (`ZiskFv/Airs/Arith/Div.lean`)
depend. Specializing the signed identity to `(na, nb, np, nr) = 0`
recovers the unsigned identity
`a_packed * b_packed + d_packed = c_packed`
(quotient × divisor + remainder = dividend).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

def Assumptions (row : ArithDivRow FGL) : Prop :=
  row.flags.na.val < 2 ∧ row.flags.nb.val < 2 ∧ row.flags.nr.val < 2
  ∧ row.flags.np.val < 2 ∧ row.flags.sext.val < 2 ∧ row.flags.m32.val < 2
  ∧ row.flags.div.val < 2 ∧ row.flags.main_div.val < 2 ∧ row.flags.main_mul.val < 2

/-- The ArithDiv per-row well-formedness Spec.

    Comprises 20 algebraic clauses: 9 boolean flag invariants
    + 3 sign-product witness pins + 8 packed-product chunk equations
    matching the v1 `div_carry_chain_holds` bundle
    (`ZiskFv/Airs/Arith/Div.lean`). -/
def Spec (row : ArithDivRow FGL) : Prop :=
  -- 9 boolean flag invariants (unchanged from A8 partial port).
  row.flags.na * (1 - row.flags.na) = 0
  ∧ row.flags.nb * (1 - row.flags.nb) = 0
  ∧ row.flags.nr * (1 - row.flags.nr) = 0
  ∧ row.flags.np * (1 - row.flags.np) = 0
  ∧ row.flags.sext * (1 - row.flags.sext) = 0
  ∧ row.flags.m32 * (1 - row.flags.m32) = 0
  ∧ row.flags.div * (1 - row.flags.div) = 0
  ∧ row.flags.main_div * (1 - row.flags.main_div) = 0
  ∧ row.flags.main_mul * (1 - row.flags.main_mul) = 0
  -- 3 sign-product witnesses (constraints 6, 7, 8 — arith.pil:58-60).
  ∧ row.aux.fab
      - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
          + 4 * row.flags.na * row.flags.nb) = 0
  ∧ row.aux.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0
  ∧ row.aux.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0
  -- 8 chunk equations (constraints 31-38 — arith.pil:205-209).
  -- 31: (eq[0]) - carry[0] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_0 * row.chunks.b_0
      - row.chunks.c_0
      + 2 * row.flags.np * row.chunks.c_0
      + row.flags.div * row.chunks.d_0
      - 2 * row.flags.nr * row.chunks.d_0
      - row.aux.carry_0 * 65536 = 0
  -- 32: (eq[1]) + carry[0] - carry[1] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_1 * row.chunks.b_0
      + row.aux.fab * row.chunks.a_0 * row.chunks.b_1
      - row.chunks.c_1
      + 2 * row.flags.np * row.chunks.c_1
      + row.flags.div * row.chunks.d_1
      - 2 * row.flags.nr * row.chunks.d_1
      + row.aux.carry_0
      - row.aux.carry_1 * 65536 = 0
  -- 33: (eq[2]) + carry[1] - carry[2] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_2 * row.chunks.b_0
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
      - row.aux.carry_2 * 65536 = 0
  -- 34: (eq[3]) + carry[2] - carry[3] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_3 * row.chunks.b_0
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
      - row.aux.carry_3 * 65536 = 0
  -- 35: (eq[4]) + carry[3] - carry[4] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_3 * row.chunks.b_1
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
      - row.aux.carry_4 * 65536 = 0
  -- 36: (eq[5]) + carry[4] - carry[5] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_3 * row.chunks.b_2
      + row.aux.fab * row.chunks.a_2 * row.chunks.b_3
      + row.chunks.a_1 * row.aux.nb_fa * (1 - row.flags.m32)
      + row.chunks.b_1 * row.aux.na_fb * (1 - row.flags.m32)
      - row.chunks.d_1 * (1 - row.flags.div)
      + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
      + row.aux.carry_4
      - row.aux.carry_5 * 65536 = 0
  -- 37: (eq[6]) + carry[5] - carry[6] * 65536 = 0
  ∧ row.aux.fab * row.chunks.a_3 * row.chunks.b_3
      + row.chunks.a_2 * row.aux.nb_fa * (1 - row.flags.m32)
      + row.chunks.b_2 * row.aux.na_fb * (1 - row.flags.m32)
      - row.chunks.d_2 * (1 - row.flags.div)
      + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
      + row.aux.carry_5
      - row.aux.carry_6 * 65536 = 0
  -- 38: (eq[7]) + carry[6] = 0  (no further carry)
  ∧ 65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
      + row.chunks.a_3 * row.aux.nb_fa * (1 - row.flags.m32)
      + row.chunks.b_3 * row.aux.na_fb * (1 - row.flags.m32)
      - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
      - row.chunks.d_3 * (1 - row.flags.div)
      + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
      + row.aux.carry_6 = 0

end ZiskFv.AirsClean.ArithDiv
