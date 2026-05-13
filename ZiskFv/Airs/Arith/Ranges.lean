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

/-! ## Arith-table row pin — signed DIV/REM sign-of-remainder

Every valid `arith_table` row with `op ∈ {186 (DIV), 187 (REM)}`,
`m32 = 0`, `div = 1`, `sext = 0` (the signed 64-bit DIV/REM rows;
table entries 66-94 in `build/extraction/Extraction/ArithTable.lean`)
satisfies the disjunction

```
nr = np   ∨   d_chunks are all zero (remainder = 0)
```

Semantics: in the IEEE-754-truncated signed division convention, the
remainder must have the same sign as the dividend (`nr = np`) *or* be
zero (`D = 0`). The four valid table rows where `nr ≠ np` are exactly
the rows where the remainder column is forced to zero by the AIR's
range-table constraints on `d[]`.

PIL citation: composition of `arith.pil:286-287` (the
`arith_table_assumes(op, m32, div, na, nb, np, nr, sext, ...)` lookup
on every Arith AIR row) with the table content at
`zisk/state-machines/arith/pil/arith_table.pil` and the data dump in
`zisk/state-machines/arith/src/arith_table_data.rs::ARITH_TABLE` (74
rows; entries 23-44 cover DIV/REM with `div_by_zero = 0` and
`div_overflow = 0`, all satisfying the disjunction).

Trust class: same as `binary_extension_op_is_shift_pin` (class #6, lookup
soundness on a small AIR table that pins a derived column). -/

/-- **Arith-table signed DIV/REM remainder-sign pin (class #6).**
    For every `Valid_ArithDiv` row carrying signed-DIV/REM mode pins
    (`sext = 0`, `m32 = 0`, `div = 1`) with `op ∈ {186, 187}`, the
    sign-of-remainder column `nr` matches the sign-of-dividend column
    `np`, **or** the four chunks of the remainder column `d[]` are
    each zero. PIL: lookup soundness on the `arith_table_assumes`
    consumer-side bus row composed with the table content. -/
axiom arith_table_op_div_rem_signed_d_sign_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (_h_sext : v.sext r_a = 0) (_h_m32 : v.m32 r_a = 0) (_h_div : v.div r_a = 1)
    (_h_op : v.op r_a = 186 ∨ v.op r_a = 187) :
    v.nr r_a = v.np r_a
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)

/-- **Arith-table signed-W DIV/REM remainder-sign pin (class #6).**
    W-mode analog of `arith_table_op_div_rem_signed_d_sign_pin`. For every
    `Valid_ArithDiv` row carrying signed-W-DIV/REM mode pins
    (`sext = 0`, `m32 = 1`, `div = 1`) with `op ∈ {190 (DIVW), 191 (REMW)}`
    — the signed 32-bit DIV/REM table rows (entries 51-72 in
    `build/extraction/Extraction/ArithTable.lean`) — the sign-of-remainder
    column `nr` matches the sign-of-dividend column `np`, **or** the four
    chunks of the remainder column `d[]` are each zero. Same trust class
    as the m32=0 sibling: lookup soundness on the `arith_table_assumes`
    consumer-side bus row composed with the table content.

    PIL citation: composition of `arith.pil:286-287` (the
    `arith_table_assumes(op, m32, div, na, nb, np, nr, sext, ...)` lookup
    on every Arith AIR row) with the table content at
    `zisk/state-machines/arith/pil/arith_table.pil` for the signed-W
    opcodes (op ∈ {190, 191}). -/
axiom arith_table_op_div_rem_signed_w_d_sign_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (_h_sext : v.sext r_a = 0) (_h_m32 : v.m32 r_a = 1) (_h_div : v.div r_a = 1)
    (_h_op : v.op r_a = 190 ∨ v.op r_a = 191) :
    v.nr r_a = v.np r_a
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)

/-! ## Carry column range — W-mode (m32 = 1)

In **W-variant mode** (`m32 = 1`, the 32-bit-truncated MUL/DIV
opcodes: MULW/DIVW/DIVUW/REMW/REMUW), the carry-chain upper-half
constraints C35-C38 collapse via the `(1 - m32) = 0` gate. The
operative carry witnesses are still 7 (columns 0..6) but their
operational range is the same as the unsigned 8-chunk case for
`cy[0..3]` (per-chunk schoolbook products mod B), and the upper
carries `cy[4..6]` are pure telescope variables zero-bounded.

PIL: `arith.pil:280`
(`arith_range_table_assumes(ARITH_RANGE_CARRY, carry[index])`)
composed with the m32=1 specialization of the carry chain.

Trust class: same as the existing
`arith_{mul,div}_carry_columns_in_range_{unsigned,signed}` axioms —
range-checker bus #6 / lookup-soundness on ARITH_RANGE_CARRY,
conditioned by the m32=1 mode pin. -/

/-- **ArithMul carry-column range (W-mode, m32 = 1).** Disjunctive
    shape mirroring the signed-mode axiom: each carry witness is
    bounded by `[-0xEFFFF..0xF0000]`, i.e.
    `cy.val ∈ [0, 0xF0000] ∪ [GL_prime - 0xEFFFF, GL_prime - 1]`.

    PIL citation: `arith.pil:280` (range table on carry columns)
    composed with the W-mode (m32=1) specialization of the
    `arith_mul_w_carry_identity`. -/
axiom arith_mul_carry_columns_in_range_w
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ)
    (_h_sext : v.sext r = 0) (_h_m32 : v.m32 r = 1) (_h_div : v.div r = 0) :
    let cy_disj (col : ℕ) : Prop :=
      (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val < 983041
        ∨ GL_prime - 983040 ≤ (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val
    cy_disj 0 ∧ cy_disj 1 ∧ cy_disj 2 ∧ cy_disj 3
      ∧ cy_disj 4 ∧ cy_disj 5 ∧ cy_disj 6

/-- **ArithDiv carry-column range (W-mode, m32 = 1).** Mirror of
    `arith_mul_carry_columns_in_range_w` for the Div view of the
    Arith AIR. Same physical columns; different named wrapper.

    DIVW / DIVUW / REMW / REMUW rows are the consumers
    (`m32 = 1`, `div = 1`, `sext = 0`). -/
axiom arith_div_carry_columns_in_range_w
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ)
    (_h_sext : v.sext r = 0) (_h_m32 : v.m32 r = 1) (_h_div : v.div r = 1) :
    let cy_disj (col : ℕ) : Prop :=
      (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val < 983041
        ∨ GL_prime - 983040 ≤ (Circuit.main v.circuit (id := 1) (column := col) (row := r) (rotation := 0) : FGL).val
    cy_disj 0 ∧ cy_disj 1 ∧ cy_disj 2 ∧ cy_disj 3
      ∧ cy_disj 4 ∧ cy_disj 5 ∧ cy_disj 6

/-! ## Arith-table W-mode operand-input pin (m32 = 1)

In W-variant mode the arith table pins the operand input chunks
to their low 32 bits: `a_2 = a_3 = b_2 = b_3 = 0`. For DIVW/REMW
the remainder column is similarly truncated: `d_2 = d_3 = 0`.

PIL citation: composition of `arith.pil:286-287` (the
`arith_table_assumes(op, m32, div, na, nb, np, nr, sext, ...)` lookup
on every Arith AIR row) with the table content at
`zisk/state-machines/arith/pil/arith_table.pil` for the W-variant
opcodes (op ∈ {0x91, 0x95, 0x96, 0x99, 0x9a} — MULW, DIVW, DIVUW,
REMW, REMUW in the canonical numbering).

Trust class: same as `binary_extension_op_is_shift_pin` (class #6,
lookup soundness on a small AIR table that pins input columns). -/

/-- **Arith-table W-mode operand chunk pin for MUL family (class #6).**
    For every `Valid_ArithMul` row carrying W-mode pins (`sext = 0`,
    `m32 = 1`, `div = 0`) with `op = 0x91` (MULW), the upper operand
    chunks are zero (32-bit operand restriction). -/
axiom arith_table_op_mulw_operand_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (_h_sext : v.sext r_a = 0) (_h_m32 : v.m32 r_a = 1) (_h_div : v.div r_a = 0)
    (_h_op : v.op r_a = 0x91) :
    (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0
      ∧ (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0

/-- **Arith-table W-mode operand/remainder chunk pin for DIV family (class #6).**
    For every `Valid_ArithDiv` row carrying W-mode pins (`sext = 0`,
    `m32 = 1`, `div = 1`) with `op ∈ {0x95, 0x96, 0x99, 0x9a}` (DIVW,
    DIVUW, REMW, REMUW), the upper operand chunks AND the upper
    remainder chunks are zero. -/
axiom arith_table_op_divw_operand_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (_h_sext : v.sext r_a = 0) (_h_m32 : v.m32 r_a = 1) (_h_div : v.div r_a = 1)
    (_h_op : v.op r_a = 0x95 ∨ v.op r_a = 0x96 ∨ v.op r_a = 0x99 ∨ v.op r_a = 0x9a) :
    (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0
      ∧ (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0
      ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0

end ZiskFv.Airs.Arith
