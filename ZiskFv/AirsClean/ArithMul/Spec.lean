import ZiskFv.AirsClean.ArithMul.Row

/-!
# ArithMul Spec + Assumptions (boolean flags + 4-limb carry chain)

ArithMul's per-row content covers:

1. 9 boolean flag constraints on `na`, `nb`, `nr`, `np`, `sext`, `m32`,
   `div`, `main_div`, `main_mul` (constraints 40-45 + `constraint_2` +
   `main_mul`/`main_div` booleans).
2. The 4-limb (8-chunk × 16-bit) carry-chain identity `a · b = c + d · 2^64`,
   parameterized by the sign-product helper columns `fab`, `na_fb`,
   `nb_fa` (cols 30–32) and 7 carry witnesses (cols 0–6). The
   helpers are pinned to `1 − 2·na − 2·nb + 4·na·nb`,
   `na · (1 − 2·nb)`, `nb · (1 − 2·na)` by constraints 6/7/8.

Each clause below mirrors the corresponding `constraint_N_every_row`
in `build/extraction/Extraction/Arith.lean` after substituting the
named accessor for the corresponding `Circuit.main … (column := N)`
expression.

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
  -- 9 boolean flag constraints (constraints 40–45 + 2 main + div).
  row.flags.na * (1 - row.flags.na) = 0
  ∧ row.flags.nb * (1 - row.flags.nb) = 0
  ∧ row.flags.nr * (1 - row.flags.nr) = 0
  ∧ row.flags.np * (1 - row.flags.np) = 0
  ∧ row.flags.sext * (1 - row.flags.sext) = 0
  ∧ row.flags.m32 * (1 - row.flags.m32) = 0
  ∧ row.flags.div * (1 - row.flags.div) = 0
  ∧ row.flags.main_div * (1 - row.flags.main_div) = 0
  ∧ row.flags.main_mul * (1 - row.flags.main_mul) = 0
  -- Constraint 6: fab − ((1 − 2·na) − 2·nb + 4·na·nb) = 0.
  ∧ row.carries.fab - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
        + 4 * row.flags.na * row.flags.nb) = 0
  -- Constraint 7: na_fb − na·(1 − 2·nb) = 0.
  ∧ row.carries.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0
  -- Constraint 8: nb_fa − nb·(1 − 2·na) = 0.
  ∧ row.carries.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0
  -- Constraint 31: (fab·a_0·b_0 − c_0) + 2·np·c_0 + div·d_0
  --                − 2·nr·d_0 − carry_0·65536 = 0.
  ∧ row.carries.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.carries.carry_0 * 65536 = 0
  -- Constraint 32: (fab·a_1·b_0 + fab·a_0·b_1 − c_1) + 2·np·c_1
  --                + div·d_1 − 2·nr·d_1 + carry_0 − carry_1·65536 = 0.
  ∧ row.carries.fab * row.chunks.a_1 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.carries.carry_0
        - row.carries.carry_1 * 65536 = 0
  -- Constraint 33 (extended; see arith.pil:207, chunk index 2).
  ∧ row.carries.fab * row.chunks.a_2 * row.chunks.b_0
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
        - row.carries.carry_2 * 65536 = 0
  -- Constraint 34 (chunk index 3).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_0
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
        - row.carries.carry_3 * 65536 = 0
  -- Constraint 35 (chunk index 4 — half-byte boundary; brings in
  --   `na·nb·m32` and `(1 - m32)` selectors).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_1
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
        - row.carries.carry_4 * 65536 = 0
  -- Constraint 36 (chunk index 5).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.carries.carry_4
        - row.carries.carry_5 * 65536 = 0
  -- Constraint 37 (chunk index 6).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.carries.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.carries.carry_5
        - row.carries.carry_6 * 65536 = 0
  -- Constraint 38 (chunk index 7, final).
  ∧ 65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.carries.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.carries.carry_6 = 0

end ZiskFv.AirsClean.ArithMul
