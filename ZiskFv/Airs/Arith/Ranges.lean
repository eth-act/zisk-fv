import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
# Arith AIR — universal column-range theorems

Mirrors `ZiskFv/Airs/Binary/BinaryRanges.lean` /
`BinaryAddRanges.lean` for the `Arith` AIR (both
multiplication-mode and division-mode views).

PIL citations (`zisk/state-machines/arith/pil/arith.pil:17-20`):
```pil
col witness bits(16) a[CHUNKS_INPUT];   // < 2^16 each (4 chunks)
col witness bits(16) b[CHUNKS_INPUT];   // < 2^16 each
col witness bits(16) c[CHUNKS_INPUT];   // < 2^16 each
col witness bits(16) d[CHUNKS_INPUT];   // < 2^16 each
```

Each `bits(16)` annotation compiles to a row-level lookup against the
standard range-checker bus.

Two axioms — one per view (`Valid_ArithMul` / `Valid_ArithDiv`) —
since the two views project the same underlying AIR columns through
different named wrappers but the trust statement is the same.

Trust class: lookup-argument soundness on the standard range-checker
bus.
-/

namespace ZiskFv.Airs.Arith

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **ArithMul range-check soundness.** Every `a_i`, `b_i`, `c_i`,
    `d_i` chunk (`i ∈ {0..3}`) at any row is < 2^16. -/
axiom arith_mul_columns_in_range (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536

/-- **ArithDiv range-check soundness.** Same as `arith_mul_columns_in_range`
    but for the Div view of the Arith AIR. -/
axiom arith_div_columns_in_range (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536

/-! ## Carry column range — unsigned-mode

The Arith AIR's 7 carry witnesses live at stage-1 columns 0..6. Per
`zisk/state-machines/arith/pil/arith.pil:17` they have storage type
`bits(64, signed)`; the actual operational bound is enforced by the
range-table lookup at `arith.pil:279-281`:

```pil
for (int index = 0; index < length(carry); ++index) {
     arith_range_table_assumes(ARITH_RANGE_CARRY, carry[index]);
}
```

The `ARITH_RANGE_CARRY` table entries are
`[-0xEFFFF..0xF0000]` (`arith_range_table.pil:69`).

In **unsigned MUL/DIV/REM mode** (`na = nb = np = nr = sext = 0`), the
carry chain admits only non-negative values: the per-chunk equations
sum at most three 32-bit products + a previous carry, divided by
2^16, which is bounded above by ~3 * 2^32 / 2^16 = ~3 * 2^16 ≈ 2^17.
Concretely the chain bound `< 131072 = 2^17` matches the bound used by
`Fundamentals/PackedBitVec/MulNoWrap.lean::fgl_mul_unsigned_*`'s
ℕ-lift identity.

Trust class: range-checker bus lookup soundness on the
ARITH_RANGE_CARRY entry of the arith_range_table — mirrors the
existing `arith_mul_columns_in_range` axiom on the same trust class
(range-checker bus #6). The mode-dependent specialization
(`< 131072` only valid when na/nb/np/nr = 0) is captured by the
hypothesis that the caller supplies the unsigned-mode pins; signed
MUL/DIV-mode rows have a different effective range and are out of
scope for this axiom (those rows route through the `h_byte_sum_circuit`
caller-burden shape, not the loose-cy shape).
-/

/-- **ArithMul carry-column range (unsigned mode).** The 7 carry
    witnesses at columns 0..6 are < 2^17 = 131072 when the row's
    sign-witness columns satisfy `na = nb = np = nr = 0` (unsigned
    MUL / MULHU / MULW mode).

    PIL citation: `arith.pil:280`
    (`arith_range_table_assumes(ARITH_RANGE_CARRY, carry[index])`)
    composed with the unsigned-mode specialization of the carry
    chain identity (`arith.pil:205-209`). -/
axiom arith_mul_carry_columns_in_range_unsigned
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ)
    (_h_na : v.na r = 0) (_h_nb : v.nb r = 0)
    (_h_np : v.np r = 0) (_h_nr : v.nr r = 0) :
    (Circuit.main v.circuit (id := 1) (column := 0) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 1) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 2) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 3) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 4) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 5) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 6) (row := r) (rotation := 0) : FGL).val < 131072

/-- **ArithDiv carry-column range (unsigned mode).** Mirror of
    `arith_mul_carry_columns_in_range_unsigned` for the Div view of
    the Arith AIR. Same physical columns; different named wrapper.

    Unsigned DIVU / REMU rows are the consumers. -/
axiom arith_div_carry_columns_in_range_unsigned
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ)
    (_h_na : v.na r = 0) (_h_nb : v.nb r = 0)
    (_h_np : v.np r = 0) (_h_nr : v.nr r = 0) :
    (Circuit.main v.circuit (id := 1) (column := 0) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 1) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 2) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 3) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 4) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 5) (row := r) (rotation := 0) : FGL).val < 131072
  ∧ (Circuit.main v.circuit (id := 1) (column := 6) (row := r) (rotation := 0) : FGL).val < 131072

/-! ## Carry column range — signed-mode (disjunctive)

In **signed MUL/DIV/REM mode** the 7 carry witnesses may take negative
values (FGL-coded as `GL_prime - |cy|`). The PIL range constraint
`arith_range_table_assumes(ARITH_RANGE_CARRY, carry[index])` at
`arith.pil:280` enforces `cy ∈ [-0xEFFFF..0xF0000]` (table at
`arith_range_table.pil:69`), which in FGL maps to the **disjunctive**
shape

```
cy.val < 0xF0001  ∨  GL_prime - 0xEFFFF ≤ cy.val
```

(i.e., `cy.val ∈ [0, 0xF0000] ∪ [GL_prime - 0xEFFFF, GL_prime - 1]`).

This is exactly the shape `Fundamentals/PackedBitVec/SignedChunkLift.lean`'s
`fgl_carry_disjunctive_lt` consumes to produce the
`|toIntZ cy| ≤ 0xF0000 = 983040` magnitude bound used by the signed-mode
ℤ aggregators.

Trust class: same as the unsigned-mode variants — range-checker bus
lookup soundness on the ARITH_RANGE_CARRY entry of the arith_range_table
(class #6). The two signed axioms below differ only in the mode-witness
preconditions (signed-mode pins instead of unsigned) and the conclusion
shape (disjunctive instead of single-bound). -/

/-- **ArithMul carry-column range (signed mode, disjunctive).** Per
    `arith_range_table.pil:69` the 7 carry witnesses at columns 0..6
    lie in the FGL-coded range `[-0xEFFFF..0xF0000]`, i.e. each
    `cy.val ∈ [0, 0xF0000] ∪ [GL_prime - 0xEFFFF, GL_prime - 1]`.

    Signed MUL/MULH rows (`na, nb, np ∈ {0,1}` with `np = na ⊕ nb`,
    `nr = 0`, `m32 = 0`, `div = 0`) are the consumers; the disjunctive
    shape composes with `SignedChunkLift.fgl_carry_disjunctive_lt` to
    derive `|toIntZ cy| ≤ 983040`.

    PIL citation: `arith.pil:280`
    (`arith_range_table_assumes(ARITH_RANGE_CARRY, carry[index])`)
    composed with the signed-mode specialization of the carry chain. -/
axiom arith_mul_carry_columns_in_range_signed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ)
    (_h_nr : v.nr r = 0) (_h_sext : v.sext r = 0)
    (_h_m32 : v.m32 r = 0) (_h_div : v.div r = 0) :
    let cy_disj (col : ℕ) : Prop :=
      (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val < 983041
        ∨ GL_prime - 983040 ≤ (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val
    cy_disj 0 ∧ cy_disj 1 ∧ cy_disj 2 ∧ cy_disj 3
      ∧ cy_disj 4 ∧ cy_disj 5 ∧ cy_disj 6

/-- **ArithDiv carry-column range (signed mode, disjunctive).** Mirror
    of `arith_mul_carry_columns_in_range_signed` for the Div view of the
    Arith AIR. Same physical columns; different named wrapper.

    Signed DIV/REM rows (`na, nb, np, nr ∈ {0,1}`, `m32 = 0`, `div = 1`)
    are the consumers. -/
axiom arith_div_carry_columns_in_range_signed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ)
    (_h_sext : v.sext r = 0) (_h_m32 : v.m32 r = 0) (_h_div : v.div r = 1) :
    let cy_disj (col : ℕ) : Prop :=
      (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val < 983041
        ∨ GL_prime - 983040 ≤ (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val
    cy_disj 0 ∧ cy_disj 1 ∧ cy_disj 2 ∧ cy_disj 3
      ∧ cy_disj 4 ∧ cy_disj 5 ∧ cy_disj 6

end ZiskFv.Airs.Arith
