import ZiskFv.AirsClean.ArithDiv.Row
import ZiskFv.AirsClean.ArithTable
import ZiskFv.AirsClean.RangeTables

/-!
# ArithDiv Spec + Assumptions

The Clean-side spec for the Arith AIR's **DIV carry-chain sub-circuit**.

`Spec` is the genuine algebraic relation the DIV carry-chain constraints
compute: the 11 clauses that encode the 4-limb signed-dispatch division
relation `a = b * c + d` (quotient × divisor + remainder = dividend).

The 11 clauses break down as:

  * 3 sign-product witness pins (constraints 6, 7, 8 — arith.pil:58-60):
    `fab = 1 - 2na - 2nb + 4*na*nb`, `na_fb = na*(1 - 2nb)`,
    `nb_fa = nb*(1 - 2na)`.
  * 8 chunk-equations (constraints 31-38 — arith.pil:205-209): the 8
    packed-product carry equations relating the `fab * a[i] * b[j]`
    cross-terms, the signed-flag offsets (`np`, `nr`, `m32`, `div`
    selectors), the `na_fb`/`nb_fa`/`na*nb` summands, the result chunks
    `c[i]`, `d[i]`, and the seven 16-bit carries `carry[0..6]`.

These are precisely the 11 PIL constraints on which
`arith_div_unsigned_packed_correct` / `arith_div_signed_packed_correct`
(`ZiskFv/Airs/Arith/Div.lean`) depend, and the 11 conjuncts of the
hand-rolled `div_carry_chain_holds` predicate. Specializing the signed
identity to `(na, nb, np, nr) = 0` recovers the unsigned identity
`a_packed * b_packed + d_packed = c_packed`.

**Scope note.** The 9 AIR-global flag-booleanity constraints
(`na/nb/nr/np/sext/m32/div/main_div/main_mul` boolean) are *not* part
of this Component's `Spec`: they belong to the Arith AIR's flag-
validation sub-circuit, on which the division carry-chain relation is
independent. ZisK's DIV verification chain pins those flag *values*
through the `arith_table` lookup axioms (`Compliance/Wrappers/Div.lean`),
never through the boolean `assertZero`s. This Component therefore
renders the DIV carry-chain sub-circuit faithfully — the curated
constraint subset that the per-opcode verification actually consumes —
exactly as the `ArithDivRow` type is itself a curated DIV view of the
Arith AIR's columns.

## Trust note

No axioms. Pure definitional content.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

/-- Assumptions on an ArithDiv row, as expected by the Clean Component.

    `True` (plan decision D-2 / finding F-4): a Component carries no
    soundness-assumptions. The 11-clause carry-chain `Spec` follows from
    the 11 definitional `assertZero` constraints alone — no range
    reasoning, no flag-value pins. -/
@[reducible]
def Assumptions (_row : ArithDivRow FGL) : Prop := True

/-- The ArithDiv DIV carry-chain Spec — the genuine 11-clause algebraic
    division relation.

    Comprises 3 sign-product witness pins (constraints 6, 7, 8) + 8
    packed-product chunk equations (constraints 31-38), matching the
    v1 `div_carry_chain_holds` bundle (`ZiskFv/Airs/Arith/Div.lean`)
    clause-for-clause. -/
@[reducible]
def Spec (row : ArithDivRow FGL) : Prop :=
  -- 3 sign-product witnesses (constraints 6, 7, 8 — arith.pil:58-60).
  row.aux.fab
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

/-- Booleanity and selector-disjointness constraints of the completed ArithDiv mirror
    (generated constraints 0--5 and 39--45). -/
@[reducible]
def ModeSpec (row : ArithDivRow FGL) : Prop :=
  row.flags.main_div * (row.flags.main_div - 1) = 0
  ∧ row.flags.main_mul * (row.flags.main_mul - 1) = 0
  ∧ row.flags.main_mul * row.flags.main_div = 0
  ∧ row.flags.signed * (1 - row.flags.signed) = 0
  ∧ row.flags.div_by_zero * (1 - row.flags.div_by_zero) = 0
  ∧ row.flags.div_overflow * (1 - row.flags.div_overflow) = 0
  ∧ row.flags.div * (1 - row.flags.div) = 0
  ∧ row.flags.m32 * (1 - row.flags.m32) = 0
  ∧ row.flags.na * (1 - row.flags.na) = 0
  ∧ row.flags.nb * (1 - row.flags.nb) = 0
  ∧ row.flags.nr * (1 - row.flags.nr) = 0
  ∧ row.flags.np * (1 - row.flags.np) = 0
  ∧ row.flags.sext * (1 - row.flags.sext) = 0

/-- Div-by-zero and signed-overflow boundary equations (generated constraints 9--24). -/
@[reducible]
def BoundarySpec (row : ArithDivRow FGL) : Prop :=
  row.flags.div_by_zero * row.chunks.b_0 = 0
  ∧ row.flags.div_by_zero * row.chunks.b_1 = 0
  ∧ row.flags.div_by_zero * row.chunks.b_2 = 0
  ∧ row.flags.div_by_zero * row.chunks.b_3 = 0
  ∧ row.flags.div_by_zero * (row.chunks.a_0 - 65535) = 0
  ∧ row.flags.div_by_zero * (row.chunks.a_1 - 65535) = 0
  ∧ row.flags.div_by_zero * (row.chunks.a_2 - (1 - row.flags.m32) * 65535) = 0
  ∧ row.flags.div_by_zero * (row.chunks.a_3 - (1 - row.flags.m32) * 65535) = 0
  ∧ row.flags.div_overflow * (row.chunks.b_0 - 65535) = 0
  ∧ row.flags.div_overflow * (row.chunks.b_1 - 65535) = 0
  ∧ row.flags.div_overflow * (row.chunks.b_2 - (1 - row.flags.m32) * 65535) = 0
  ∧ row.flags.div_overflow * (row.chunks.b_3 - (1 - row.flags.m32) * 65535) = 0
  ∧ row.flags.div_overflow * row.chunks.c_0 = 0
  ∧ row.flags.div_overflow * (row.chunks.c_1 - row.flags.m32 * 32768) = 0
  ∧ row.flags.div_overflow * row.chunks.c_2 = 0
  ∧ row.flags.div_overflow * (row.chunks.c_3 - (1 - row.flags.m32) * 32768) = 0

/-- Inverse-sum witness equation detecting a nonzero divisor (generated constraint 25). -/
@[reducible]
def InverseSumSpec (row : ArithDivRow FGL) : Prop :=
  (row.flags.div - row.flags.div_by_zero) *
    (1 - row.aux.inv_sum_all_bs *
      (((row.chunks.b_0 + row.chunks.b_1) + row.chunks.b_2) + row.chunks.b_3)) = 0

/-- Scope and exceptional-mode disjointness equations (generated constraints 26--30). -/
@[reducible]
def ScopeSpec (row : ArithDivRow FGL) : Prop :=
  row.flags.div_by_zero * (1 - row.flags.div) = 0
  ∧ row.flags.div_overflow * (1 - row.flags.div) = 0
  ∧ row.flags.div_overflow * (1 - row.flags.signed) = 0
  ∧ row.flags.div_overflow * row.flags.div_by_zero = 0
  ∧ row.flags.div_by_zero * row.flags.div_overflow = 0

/-- Result mux equation (generated constraint 46). -/
@[reducible]
def C46Spec (row : ArithDivRow FGL) : Prop :=
  row.flags.bus_res1 -
    (row.flags.sext * 4294967295 + (1 - row.flags.m32) *
      (((1 - row.flags.main_mul - row.flags.main_div) *
          (row.chunks.d_2 + row.chunks.d_3 * 65536)) +
       row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
       row.flags.main_div * (row.chunks.a_2 + row.chunks.a_3 * 65536))) = 0

/-- W-mode high-lane equations (generated constraints 47--48). -/
@[reducible]
def WModeSpec (row : ArithDivRow FGL) : Prop :=
  row.flags.m32 *
    (row.flags.div * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
      (1 - row.flags.div) * (row.chunks.a_2 + row.chunks.a_3 * 65536)) = 0
  ∧ row.flags.m32 * (row.chunks.b_2 + row.chunks.b_3 * 65536) = 0

/-- All named local algebraic bundles supplied by `mainComplete`. -/
@[reducible]
def CompleteLocalSpec (row : ArithDivRow FGL) : Prop :=
  Spec row ∧ ModeSpec row ∧ BoundarySpec row ∧ InverseSumSpec row ∧ ScopeSpec row
    ∧ C46Spec row ∧ WModeSpec row

/-- The lookup half of the full ArithTable contract for this row.
    This is separated from `Spec` so the existing carry-chain re-root
    remains usable until the global theorem supplies lookup membership
    constructibly. -/
@[reducible]
def ArithTableSpec (row : ArithDivRow FGL) : Prop :=
  ArithTable.arithTable.Spec (arithTableRow row)

/-- The eight indexed `arith_range_table_assumes(range_*, chunk)` lookups
    (`arith.pil:299-306`). -/
@[reducible]
def IndexedRangeSpec (row : ArithDivRow FGL) : Prop :=
  RangeTables.arithRangeTable.Spec #v[row.flags.range_ab + 26, row.chunks.a_1]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_ab + 9, row.chunks.b_1]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_cd + 26, row.chunks.c_1]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_cd + 9, row.chunks.d_1]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_ab, row.chunks.a_3]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_ab + 17, row.chunks.b_3]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_cd, row.chunks.c_3]
  ∧ RangeTables.arithRangeTable.Spec #v[row.flags.range_cd + 17, row.chunks.d_3]

/-- Full ArithDiv row contract once ArithTable and indexed Arith range-table
    lookups are plumbed into Compliance: carry-chain algebra plus ROM
    membership and the indexed sign-range evidence. -/
@[reducible]
def FullSpec (row : ArithDivRow FGL) : Prop :=
  Spec row ∧ ArithTableSpec row ∧ IndexedRangeSpec row

end ZiskFv.AirsClean.ArithDiv
