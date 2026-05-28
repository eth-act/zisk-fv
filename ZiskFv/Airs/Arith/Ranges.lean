import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Channels.RangeBusSoundness

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
open ZiskFv.Channels.RangeBusSoundness

/-! ## ArithTable row-native projections

T5 retired the shared ArithTable lookup/permutation axioms from the
canonical closure. Opcode-specific mode and selector facts below are proved
from an explicit row-native `ArithTableSpec (rowAt v r)` witness, supplied by
the caller or a future Clean ensemble bridge.
-/


/-- **ArithMul range-check soundness (derived).** Every `a_i`, `b_i`,
    `c_i`, `d_i` chunk (`i ∈ {0..3}`) at any row is < 2^16.

    Previously an axiom; now derived from `range_bus_sound` via 16
    applications. -/
theorem arith_mul_columns_in_range (a : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact range_bus_sound a (fun a r => a.a_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.a_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.a_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.a_3 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_3 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_3 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_3 r) 16 trivial r

/-- **ArithDiv range-check soundness (derived).** Same as
    `arith_mul_columns_in_range` but for the Div view of the Arith AIR.
    Derived from `range_bus_sound` via 16 applications. -/
theorem arith_div_columns_in_range (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact range_bus_sound a (fun a r => a.a_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.a_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.a_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.a_3 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.b_3 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.c_3 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_0 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_1 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_2 r) 16 trivial r
  · exact range_bus_sound a (fun a r => a.d_3 r) 16 trivial r

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

/-- **ArithMul carry-column range (unsigned mode) (derived).** The 7
    carry witnesses at columns 0..6 are < 2^17 = 131072 when the row's
    sign-witness columns satisfy `na = nb = np = nr = 0` (unsigned
    MUL / MULHU / MULW mode).

    Previously an axiom; now derived from `range_bus_sound` with
    width=17 via 7 applications. The unsigned-mode pins are kept as
    hypotheses for downstream API compatibility but no longer needed
    by the proof (range_bus_sound applies uniformly). -/
theorem arith_mul_carry_columns_in_range_unsigned
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (_h_na : v.na r = 0) (_h_nb : v.nb r = 0)
    (_h_np : v.np r = 0) (_h_nr : v.nr r = 0) :
    (v.cy_0 r).val < 131072
  ∧ (v.cy_1 r).val < 131072
  ∧ (v.cy_2 r).val < 131072
  ∧ (v.cy_3 r).val < 131072
  ∧ (v.cy_4 r).val < 131072
  ∧ (v.cy_5 r).val < 131072
  ∧ (v.cy_6 r).val < 131072 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact range_bus_sound v (fun v r => v.cy_0 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_1 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_2 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_3 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_4 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_5 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_6 r) 17 trivial r

/-- **ArithDiv carry-column range (unsigned mode) (derived).** Mirror
    of `arith_mul_carry_columns_in_range_unsigned` for the Div view.
    Post-Phase-F4 retirement: uses the named `cy_0..cy_6` accessors. -/
theorem arith_div_carry_columns_in_range_unsigned
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (_h_na : v.na r = 0) (_h_nb : v.nb r = 0)
    (_h_np : v.np r = 0) (_h_nr : v.nr r = 0) :
    (v.cy_0 r).val < 131072
  ∧ (v.cy_1 r).val < 131072
  ∧ (v.cy_2 r).val < 131072
  ∧ (v.cy_3 r).val < 131072
  ∧ (v.cy_4 r).val < 131072
  ∧ (v.cy_5 r).val < 131072
  ∧ (v.cy_6 r).val < 131072 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact range_bus_sound v (fun v r => v.cy_0 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_1 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_2 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_3 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_4 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_5 r) 17 trivial r
  · exact range_bus_sound v (fun v r => v.cy_6 r) 17 trivial r

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
theorem arith_mul_carry_columns_in_range_signed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (_h_nr : v.nr r = 0) (_h_sext : v.sext r = 0)
    (_h_m32 : v.m32 r = 0) (_h_div : v.div r = 0) :
    ((v.cy_0 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_0 r).val)
  ∧ ((v.cy_1 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_1 r).val)
  ∧ ((v.cy_2 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_2 r).val)
  ∧ ((v.cy_3 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_3 r).val)
  ∧ ((v.cy_4 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_4 r).val)
  ∧ ((v.cy_5 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_5 r).val)
  ∧ ((v.cy_6 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_6 r).val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact signed_range_bus_sound v (fun v r => v.cy_0 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_1 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_2 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_3 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_4 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_5 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_6 r) trivial r

/-- **ArithDiv carry-column range (signed mode, disjunctive).** Mirror
    of `arith_mul_carry_columns_in_range_signed` for the Div view of the
    Arith AIR. Same physical columns; uses named accessors after Phase
    F4 retirement.

    Signed DIV/REM rows (`na, nb, np, nr ∈ {0,1}`, `m32 = 0`, `div = 1`)
    are the consumers. -/
theorem arith_div_carry_columns_in_range_signed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (_h_sext : v.sext r = 0) (_h_m32 : v.m32 r = 0) (_h_div : v.div r = 1) :
    let cy_disj (cy : FGL) : Prop :=
      cy.val < 983041 ∨ GL_prime - 983040 ≤ cy.val
    cy_disj (v.cy_0 r) ∧ cy_disj (v.cy_1 r) ∧ cy_disj (v.cy_2 r) ∧ cy_disj (v.cy_3 r)
      ∧ cy_disj (v.cy_4 r) ∧ cy_disj (v.cy_5 r) ∧ cy_disj (v.cy_6 r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact signed_range_bus_sound v (fun v r => v.cy_0 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_1 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_2 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_3 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_4 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_5 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_6 r) trivial r

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
theorem arith_mul_carry_columns_in_range_w
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (_h_m32 : v.m32 r = 1) (_h_div : v.div r = 0) :
    ((v.cy_0 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_0 r).val)
  ∧ ((v.cy_1 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_1 r).val)
  ∧ ((v.cy_2 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_2 r).val)
  ∧ ((v.cy_3 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_3 r).val)
  ∧ ((v.cy_4 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_4 r).val)
  ∧ ((v.cy_5 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_5 r).val)
  ∧ ((v.cy_6 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_6 r).val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact signed_range_bus_sound v (fun v r => v.cy_0 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_1 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_2 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_3 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_4 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_5 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_6 r) trivial r

/-- **ArithDiv carry-column range (W-mode, m32 = 1).** Mirror of
    `arith_mul_carry_columns_in_range_w` for the Div view of the
    Arith AIR. Uses named accessors after Phase F4 retirement.

    DIVW / DIVUW / REMW / REMUW rows are the consumers
    (`m32 = 1`, `div = 1`). `sext` is the W-result sign-extension
    selector, not a carry-range precondition. -/
theorem arith_div_carry_columns_in_range_w
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (_h_m32 : v.m32 r = 1) (_h_div : v.div r = 1) :
    let cy_disj (cy : FGL) : Prop :=
      cy.val < 983041 ∨ GL_prime - 983040 ≤ cy.val
    cy_disj (v.cy_0 r) ∧ cy_disj (v.cy_1 r) ∧ cy_disj (v.cy_2 r) ∧ cy_disj (v.cy_3 r)
      ∧ cy_disj (v.cy_4 r) ∧ cy_disj (v.cy_5 r) ∧ cy_disj (v.cy_6 r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact signed_range_bus_sound v (fun v r => v.cy_0 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_1 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_2 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_3 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_4 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_5 r) trivial r
  · exact signed_range_bus_sound v (fun v r => v.cy_6 r) trivial r

/-! ## Arith-table W-mode operand-input pin (m32 = 1)

In W-variant mode the arith table pins the operand input chunks
to their low 32 bits: `a_2 = a_3 = b_2 = b_3 = 0`. For DIVW/REMW
the remainder column is similarly truncated: `d_2 = d_3 = 0`.

PIL citation: composition of `arith.pil:286-287` (the
`arith_table_assumes(op, m32, div, na, nb, np, nr, sext, ...)` lookup
on every Arith AIR row) with the table content at
`zisk/state-machines/arith/pil/arith_table.pil` for the W-variant
opcodes (op ∈ {182, 188, 189, 190, 191} — MULW, DIVUW, REMUW,
DIVW, REMW in the canonical numbering).

Trust class: same as `binary_extension_op_is_shift_pin` (class #6,
lookup soundness on a small AIR table that pins input columns). -/

/-! ## Arith-table mode pin — signed non-W DIV/REM (m32 = 0)

m32=0 sibling of `arith_table_op_divw_operand_pin`. For every
`Valid_ArithDiv` row whose `op` column reads as 186 (signed DIV) or
187 (signed REM) — i.e. the signed 64-bit DIV/REM rows in
`arith_table_data.rs::ARITH_TABLE` (entries 23-33 per the dump in
`build/extraction/Extraction/ArithTable.lean:66-76`) — the table
lookup `arith_table_assumes(op, m32, div, ...)` at
`arith.pil:286-287` pins the row's mode-selector columns to the
signed-64-bit-DIV/REM mode: `sext = 0`, `m32 = 0`, `div = 1`.

Trust class: same as `arith_table_op_divw_operand_pin` (class #6,
lookup soundness on a small AIR table that pins mode-selector
columns from the `op` literal). -/

/-- **Arith-table signed non-W DIV/REM mode pin (class #6).**
    For every `Valid_ArithDiv` row with `op ∈ {186, 187}` (signed
    64-bit DIV / REM), the arith_table lookup pins
    `sext = 0`, `m32 = 0`, `div = 1`. PIL citation: composition of
    `arith.pil:286-287` (the `arith_table_assumes` lookup) with the
    table content at `arith_table.pil` (signed 64-bit DIV/REM rows).

    Consumed by `equiv_DIV` (Compliance/Wrappers/Div.lean) to
    discharge the three mode pins `h_sext`/`h_m32`/`h_div` given the
    arith-side opcode literal (which is itself a consequence of the
    OpBus permutation matching `m.op r_main` to `v.op r_a`). -/
theorem arith_table_op_div_rem_signed_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r_a))
    (h_op : v.op r_a = 186 ∨ v.op r_a = 187) :
    v.sext r_a = 0 ∧ v.m32 r_a = 0 ∧ v.div r_a = 1 :=
  ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_signed_mode_pin
    v r_a h_arith_table h_op

/-! ## Arith-table primary/secondary selector pin — signed DIV / REM (m32 = 0)

Companion to `arith_table_op_div_rem_signed_mode_pin`. The arith_table
lookup at `arith.pil:286-287` covers not just the `(sext, m32, div)`
mode triple but also the **primary/secondary selectors** `main_mul`
and `main_div` — see the explicit arguments on the
`arith_table_assumes(op, m32, div, na, nb, np, nr, sext,
div_by_zero, div_overflow, main_mul, main_div, signed,
range_ab, range_cd)` call.

Per the row-type table at `arith.pil:222-234`:

* op = 186 (signed 64-bit DIV) — **primary row**: `main_div = 1`,
  `main_mul = 0`. The bus emits the quotient lane (`a[]`).
* op = 187 (signed 64-bit REM) — **secondary row**: `main_div = 0`,
  `main_mul = 0` (`secondary = 1 - main_mul - main_div = 1`). The
  bus emits the remainder lane (`d[]`).

Trust class: same as `arith_table_op_div_rem_signed_mode_pin`
(class #6b, lookup soundness on the consumer-side `arith_table_assumes`
bus row composed with the arith_table content for signed 64-bit
DIV/REM rows). Same kind, narrower covering set. -/

/-- **Arith-table signed non-W DIV/REM primary/secondary selector pin (class #6b).**
    For every `Valid_ArithDiv` row with `op = 186` (signed 64-bit DIV),
    the arith_table lookup pins `main_div = 1`, `main_mul = 0`
    (primary lane); for `op = 187` (signed 64-bit REM), it pins
    `main_div = 0`, `main_mul = 0` (secondary lane). PIL citation:
    composition of `arith.pil:286-287` (the `arith_table_assumes`
    lookup, explicitly including `main_mul` and `main_div` columns)
    with the row-type table at `arith.pil:222-234`.

    Consumed by `equiv_DIV` (`Compliance/Wrappers/Div.lean`) to
    derive the `main_div = 1`, `main_mul = 0` pins required by
    `div_bus_res1_eq_a_hi` (`Airs/Arith/BusRes1.lean:79`) for the
     hi-lane discharge. -/
theorem arith_table_op_div_rem_main_selector_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r_a))
    (h_op : v.op r_a = 186 ∨ v.op r_a = 187) :
    (v.op r_a = 186 → v.main_div r_a = 1 ∧ v.main_mul r_a = 0)
  ∧ (v.op r_a = 187 → v.main_div r_a = 0 ∧ v.main_mul r_a = 0) :=
  ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_main_selector_pin
    v r_a h_arith_table h_op

/-! ## Arith-table signed DIV/REM sign-witness MSB pins — `np = MSB(C)`, `nb = MSB(B)`

 for the DIV pilot. The arith_table lookup at `arith.pil:286-287`
covers, among other columns, the sign-witness pair `(np, nb)`. The
row-type table at `arith.pil:222-234` for signed 64-bit DIV/REM
(`op ∈ {186, 187}`, line 232) reads:

```
//  1   0   1   1  div      rem        0xba 186  0xbb 187   a3   b3   c3   d3
```

— where the columns labeled `na`, `nb`, `np`, `nr` are set to `a3`,
`b3`, `c3`, `d3` respectively. That notation (per the legend at
`arith.pil:222-229`) means each sign-witness equals the MSB of the
correspondingly-named input/output chunk. Concretely for signed DIV,
`np = MSB(c[3])` (high bit of the dividend's top chunk = MSB of the
64-bit dividend C) and `nb = MSB(b[3])` (MSB of divisor B). The lookup
binds these as part of the row signature: every valid row in
`arith_table_data.rs::ARITH_TABLE` for op ∈ {186, 187} (entries 23-44)
sets the `np` / `nb` flag bits (positions 16 / 8 in the encoded flags
field per `arith_table_helpers.rs:130-140`) to match this MSB
convention.

Equivalently in packed-chunk form: with
`C := packed4 c[0..3]` and `B := packed4 b[0..3]`, the row admits
`np = 1` iff `C ≥ 2^63` and `nb = 1` iff `B ≥ 2^63`. Any other choice
of `np` / `nb` produces a row that's not in the lookup table.

These two pins are not consequences of the carry-chain identity alone
(it admits algebraic slack at degenerate inputs); they are
**enforced** by the arith_table lookup. Naming them as narrow
class-#6b axioms exposes the trust we already accept — same kind as
the existing `arith_table_op_div_rem_signed_d_sign_pin` (which pins
`nr` via the same lookup mechanism on the same rows) and
`arith_table_op_div_rem_main_selector_pin` (which pins the
`main_mul` / `main_div` columns via the same lookup).

Consumed by `equiv_DIV` (`Compliance/Wrappers/Div.lean`) — in
composition with the generic signed Sail-state bridge — to derive
`h_rs1_value` / `h_rs2_value` (the signed packed-lane equations connecting
`r1_val.toInt` / `r2_val.toInt` to the AIR's `C - np·2^64` /
`B - nb·2^64` columns), closing .

Trust class: same as `arith_table_op_div_rem_signed_mode_pin` and
`arith_table_op_div_rem_main_selector_pin` — class #6b, arith_table
lookup soundness pinning derived consequences on existing witness
columns. -/



/-! ## Arith-table MUL-family mode + main_mul/main_div selector pins

Mirror of the DIV-pilot pair
(`arith_table_op_div_rem_signed_mode_pin` and
`arith_table_op_div_rem_main_selector_pin`) on the MUL side of the
shared Arith AIR — class #6b, lookup soundness on the
`arith_table_assumes(op, m32, div, na, nb, np, nr, sext,
div_by_zero, div_overflow, main_mul, main_div, ...)` lookup at
`arith.pil:286-287` composed with the MUL-family rows of
`arith_table.pil` / `arith_table_data.rs::ARITH_TABLE`.

Per `zisk/pil/operations.pil:71-78`, the MUL-family opcodes are
MULU=0xb0, MULUH=0xb1, MULSUH=0xb3, MUL=0xb4, MULH=0xb5, MUL_W=0xb6
(holes 0xb2, 0xb7 are reserved-but-unused). For the **low-half**
multiply opcode MUL = 0xb4 = 180 — signed × signed → low 64 bits —
the table entry pins all seven sign / mode witnesses to 0
(`na = nb = np = nr = sext = m32 = div = 0`) because the low 64 bits
of a signed×signed product equal the low 64 bits of the corresponding
unsigned×unsigned product (sign-extension does not affect the low
64); the implementation accordingly uses the unsigned carry-chain
identity for MUL. The 64-bit high-half opcodes
MULUH/MULSUH/MULH/MULU pin different sign-witness combinations and
are NOT covered by this axiom; their respective within-shape wrappers
will need parallel pins.

The companion selector pin pins the primary/secondary lane:
`main_mul = 1, main_div = 0` for op = 180 (MUL-primary lane, the bus
emits the low product through `bus_res0`).
-/

/-- **Arith-table MUL basic mode pin (derived).**
    This is the true static subset of the MUL table rows: the lookup pins
    `nr = sext = m32 = div = 0` and booleanity of `na`, `nb`, and `np`,
    but does not pin those sign witnesses to zero. -/
theorem arith_table_op_mul_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 180) :
    v.nr r_a = 0 ∧ v.sext r_a = 0 ∧ v.m32 r_a = 0 ∧ v.div r_a = 0
      ∧ (v.na r_a = 0 ∨ v.na r_a = 1)
      ∧ (v.nb r_a = 0 ∨ v.nb r_a = 1)
      ∧ (v.np r_a = 0 ∨ v.np r_a = 1) :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mul_basic_mode_pin
    v r_a h_arith_table h_op

/-- **Arith-table MUL range pins (derived).**
    For low-half signed MUL (`op = 180`), the static table classifies
    the range-check selector columns by the sign-witness tuple:
    `range_ab` follows `(na, nb)` and `range_cd` follows `np`.

    These are faithful ROM facts only; they do not assert the dynamic
    side conditions needed to replace the old all-zero sign shortcut. -/
theorem arith_table_op_mul_range_pins
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 180) :
    (v.na r_a = 0 → v.nb r_a = 0 → v.range_ab r_a = 4)
      ∧ (v.na r_a = 1 → v.nb r_a = 0 → v.range_ab r_a = 7)
      ∧ (v.na r_a = 0 → v.nb r_a = 1 → v.range_ab r_a = 5)
      ∧ (v.na r_a = 1 → v.nb r_a = 1 → v.range_ab r_a = 8)
      ∧ (v.np r_a = 0 → v.range_cd r_a = 1)
      ∧ (v.np r_a = 1 → v.range_cd r_a = 2) :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mul_range_pins
    v r_a h_arith_table h_op

/-- **Arith-table MUL sign-product split (derived).**
    For low-half signed MUL (`op = 180`), the static ROM rows either
    satisfy the usual sign-product relation `np = na XOR nb` in field
    arithmetic, or they are one of the two exceptional negative-times-
    positive shapes with `np = 0`.

    This is only the table-side case split. The exceptional branches
    still need the dynamic carry/range argument before the old all-zero
    sign shortcut can be deleted. -/
theorem arith_table_op_mul_np_xor_or_zero_product_shape
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 180) :
    v.np r_a = v.na r_a + v.nb r_a - 2 * v.na r_a * v.nb r_a
      ∨ (v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0) :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mul_np_xor_or_zero_product_shape
    v r_a h_arith_table h_op

/-- **Arith-table MUL primary/secondary selector pin (class #6b).**
    For every `Valid_ArithMul` row with `op = 180` (MUL — low 64 bits)
    the same `arith_table_assumes` lookup at `arith.pil:286-287` pins
    the primary/secondary selectors to MUL-primary:
    `main_mul = 1, main_div = 0`.

    PIL citation: `arith.pil:286-287` (`arith_table_assumes(op, m32, div,
    na, nb, np, nr, sext, div_by_zero, div_overflow, main_mul, main_div,
    ...)` — `main_mul` and `main_div` are explicit columns in the
    lookup tuple) composed with the row-type table at
    `arith.pil:222-234` and the MUL=0xb4 row of
    `arith_table_data.rs::ARITH_TABLE` (which selects the
    low-product lane via `main_mul = 1`).

    Consumed by `equiv_MUL` to derive the MUL-primary mode
    pins (`main_mul = 1`, `main_div = 0`) required by
    `mul_bus_res1_eq_c_hi` (`Airs/Arith/BusRes1.lean:56`) for the
    hi-lane discharge of `h_byte_hi` on `equiv_MUL`. Same trust kind
    as `arith_table_op_div_rem_main_selector_pin` (the DIV analog). -/
theorem arith_table_op_mul_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 180) :
    v.main_mul r_a = 1 ∧ v.main_div r_a = 0 :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mul_main_selector_pin
    v r_a h_arith_table h_op

/-! ## Arith-table unsigned non-W DIV/REM mode pin (DIVU = 184, REMU = 185)

Companion to `arith_table_op_div_rem_signed_mode_pin` for the
**unsigned** 64-bit DIV/REM rows (`op ∈ {184, 185}`). Per the
row-type table at `arith.pil:222-234`, the unsigned-mode rows pin
all four sign-witness columns to 0 (`na = nb = np = nr = 0`) plus
the (sext, m32, div) triple to (0, 0, 1).

PIL citation: `arith.pil:286-287` (`arith_table_assumes` lookup)
composed with the DIVU = 0xb8 / REMU = 0xb9 rows of
`arith_table.pil` / `arith_table_data.rs::ARITH_TABLE`. Trust class
#6b (lookup soundness on the consumer-side `arith_table_assumes` bus
row composed with the arith_table content). Same kind, narrower
scope, as `arith_table_op_div_rem_signed_mode_pin`.
-/

/-- **Arith-table unsigned non-W DIV/REM mode pin (class #6b).**
    For every `Valid_ArithDiv` row with `op ∈ {184, 185}` (unsigned
    64-bit DIVU / REMU), the arith_table lookup pins all four sign
    witnesses to 0, plus `sext = 0`, `m32 = 0`, `div = 1`. -/
theorem arith_table_op_div_rem_unsigned_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r_a))
    (h_op : v.op r_a = 184 ∨ v.op r_a = 185) :
    v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0 ∧ v.nr r_a = 0
      ∧ v.sext r_a = 0 ∧ v.m32 r_a = 0 ∧ v.div r_a = 1 :=
  ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_unsigned_mode_pin
    v r_a h_arith_table h_op

/-- **Arith-table unsigned non-W DIV/REM primary/secondary selector pin (class #6b).**
    For every `Valid_ArithDiv` row with `op = 184` (DIVU), the
    arith_table lookup pins `main_div = 1, main_mul = 0` (primary
    lane); for `op = 185` (REMU), it pins `main_div = 0, main_mul = 0`
    (secondary lane). PIL citation: same as
    `arith_table_op_div_rem_main_selector_pin` modulo the row-table
    rows for `op = 184 / 185`. -/
theorem arith_table_op_div_rem_unsigned_main_selector_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r_a))
    (h_op : v.op r_a = 184 ∨ v.op r_a = 185) :
    (v.op r_a = 184 → v.main_div r_a = 1 ∧ v.main_mul r_a = 0)
  ∧ (v.op r_a = 185 → v.main_div r_a = 0 ∧ v.main_mul r_a = 0) :=
  ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_unsigned_main_selector_pin
    v r_a h_arith_table h_op

/-! ## Arith-table W-mode DIV/REM mode pins (m32 = 1)

W-mode (m32 = 1) analogs of `arith_table_op_div_rem_unsigned_mode_pin`
and `arith_table_op_div_rem_signed_mode_pin`. Per the row-type table at
`arith.pil:222-234`, the W-variant DIV/REM rows pin:

* `op ∈ {188 (DIVUW), 189 (REMUW)}` — unsigned-W: all four sign
  witnesses zero, plus `(sext, m32, div) = (0, 1, 1)`.
* `op ∈ {190 (DIVW), 191 (REMW)}` — signed-W: `(sext, m32, div) =
  (0, 1, 1)`; `na, nb, np, nr` carry sign witnesses (na = MSB(a3-cohort),
  nb = MSB(b3-cohort), np = MSB(c3-cohort), nr = MSB(d3-cohort) per
  the row-type legend).

Selector-pin companions pin `main_div = 1, main_mul = 0` for the
primary (DIVUW/DIVW) lanes and `main_div = 0, main_mul = 0` for the
secondary (REMUW/REMW) lanes.

Trust class: same as `arith_table_op_div_rem_unsigned_mode_pin`
(class #6b, lookup soundness on the consumer-side `arith_table_assumes`
bus row composed with the arith_table content for the corresponding
W-variant rows). PIL citation: `arith.pil:286-287`
(`arith_table_assumes(op, m32, div, na, nb, np, nr, sext,
div_by_zero, div_overflow, main_mul, main_div, ...)`) composed with
the W-variant rows of `arith_table.pil` /
`arith_table_data.rs::ARITH_TABLE`.
-/

/-- **Arith-table unsigned-W DIV/REM basic mode pin (derived).**
    True static subset of the unsigned W rows. `sext` is intentionally not
    pinned here: concrete ROM rows include both `sext = 0` and `sext = 1`. -/
theorem arith_table_op_div_rem_unsigned_w_basic_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r_a))
    (h_op : v.op r_a = 188 ∨ v.op r_a = 189) :
    v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0 ∧ v.nr r_a = 0
      ∧ v.m32 r_a = 1 ∧ v.div r_a = 1 :=
  ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_unsigned_w_basic_mode_pin
    v r_a h_arith_table h_op

/-- **Arith-table signed-W DIV/REM basic mode pin (derived).**
    True static subset of the signed W rows. `sext` is intentionally not
    pinned here: the table contains sign-extending rows. -/
theorem arith_table_op_div_rem_signed_w_basic_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r_a))
    (h_op : v.op r_a = 190 ∨ v.op r_a = 191) :
    v.m32 r_a = 1 ∧ v.div r_a = 1 :=
  ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_signed_w_basic_mode_pin
    v r_a h_arith_table h_op

/-! ## Arith-table MULHU mode pin (op = 0xb1 = 177)

Companion to `arith_table_op_mul_mode_pin`. For the **unsigned**
64-bit high-half MUL row (`op = 177`, MULHU = MULUH), the arith_table
lookup pins all seven mode columns to 0 — unsigned × unsigned, no
sign witnesses needed; full 128-bit product is computed by the
unsigned carry chain, and the high half is observed via the
secondary bus emission's `d[]` chunks rather than the primary `c[]`.

PIL citation: `arith.pil:286-287` (`arith_table_assumes` lookup)
composed with the MULUH = 0xb1 row of `arith_table_data.rs::ARITH_TABLE`.

Trust class #6b (lookup soundness on the consumer-side
`arith_table_assumes` bus row composed with the arith_table content).
Same kind, narrower scope, as `arith_table_op_mul_mode_pin`.
-/

/-- **Arith-table MULHU mode pin (class #6b).**
    For every `Valid_ArithMul` row with `op = 177` (MULHU — unsigned
    high half), the arith_table lookup pins all seven mode columns
    to 0 (`na = nb = np = nr = sext = m32 = div = 0`). PIL citation:
    `arith.pil:286-287` composed with the MULUH=0xb1 row of
    `arith_table_data.rs::ARITH_TABLE`. -/
theorem arith_table_op_mulhu_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 177) :
    v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0 ∧ v.nr r_a = 0
      ∧ v.sext r_a = 0 ∧ v.m32 r_a = 0 ∧ v.div r_a = 0 :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulhu_mode_pin
    v r_a h_arith_table h_op

/-- **Arith-table MULHU primary/secondary selector pin (class #6b).**
    For every `Valid_ArithMul` row with `op = 177` (MULHU), the same
    `arith_table_assumes` lookup at `arith.pil:286-287` pins the
    primary/secondary selectors to MULHU-secondary:
    `main_mul = 0, main_div = 0`. The MULHU row in
    `arith_table_data.rs::ARITH_TABLE` selects the high-product
    lane via `main_mul = 0` (so `secondary = 1 - main_mul - main_div = 1`).

    Consumed by `equiv_MULHU` to derive the secondary-mode
    pins (`main_mul = 0`, `main_div = 0`) required by
    `mulh_bus_res1_eq_d_hi` (`Airs/Arith/BusRes1.lean`) for the
    hi-lane discharge of `h_byte_hi`. Same trust kind as
    `arith_table_op_mul_main_selector_pin` (the low-half MUL analog). -/
theorem arith_table_op_mulhu_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 177) :
    v.main_mul r_a = 0 ∧ v.main_div r_a = 0 :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulhu_main_selector_pin
    v r_a h_arith_table h_op

/-! ## Arith-table signed high-half MUL mode projections (MULH = 181, MULHSU = 179)

Faithful static projections for the **signed** / **mixed-sign** 64-bit
high-half MUL rows.

* **MULH (op = 181):** signed × signed. `nr = sext = m32 = div = 0`;
  `na` / `nb` / `np` are boolean sign-witness columns (NOT pinned to 0).
  The old `np = na XOR nb` claim is not a static ROM fact.
* **MULHSU (op = 179):** signed × unsigned. As for MULH but with `nb`
  additionally pinned to 0 (rs2 is interpreted as unsigned).

PIL citation: `arith.pil:286-287` (`arith_table_assumes` lookup)
composed with the MULH=0xb5 / MULHSU=0xb3 rows of
`arith_table_data.rs::ARITH_TABLE`.
-/

/-- **Arith-table MULH basic mode pin (derived).**
    True static subset of the MULH rows: mode pins plus booleanity of the
    sign witnesses. The XOR/product-sign relation is not a static ROM fact. -/
theorem arith_table_op_mulh_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 181) :
    v.nr r_a = 0 ∧ v.sext r_a = 0 ∧ v.m32 r_a = 0 ∧ v.div r_a = 0
      ∧ (v.na r_a = 0 ∨ v.na r_a = 1)
      ∧ (v.nb r_a = 0 ∨ v.nb r_a = 1)
      ∧ (v.np r_a = 0 ∨ v.np r_a = 1) :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulh_basic_mode_pin
    v r_a h_arith_table h_op

/-- **Arith-table MULH primary/secondary selector pin (class #6b).**
    For every `Valid_ArithMul` row with `op = 181` (MULH), the same
    `arith_table_assumes` lookup pins the primary/secondary selectors
    to MULH-secondary: `main_mul = 0, main_div = 0`. -/
theorem arith_table_op_mulh_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 181) :
    v.main_mul r_a = 0 ∧ v.main_div r_a = 0 :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulh_main_selector_pin
    v r_a h_arith_table h_op

/-- **Arith-table MULHSU basic mode pin (derived).**
    True static subset of the MULHSU rows: unsigned second operand, mode
    pins, and booleanity of the remaining sign witnesses. The product-sign
    XOR relation is not a static ROM fact. -/
theorem arith_table_op_mulhsu_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 179) :
    v.nb r_a = 0
      ∧ v.nr r_a = 0 ∧ v.sext r_a = 0 ∧ v.m32 r_a = 0 ∧ v.div r_a = 0
      ∧ (v.na r_a = 0 ∨ v.na r_a = 1)
      ∧ (v.np r_a = 0 ∨ v.np r_a = 1) :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulhsu_basic_mode_pin
    v r_a h_arith_table h_op

/-- **Arith-table MULHSU primary/secondary selector pin (class #6b).**
    For every `Valid_ArithMul` row with `op = 179` (MULHSU), the same
    `arith_table_assumes` lookup pins `main_mul = 0, main_div = 0`. -/
theorem arith_table_op_mulhsu_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 179) :
    v.main_mul r_a = 0 ∧ v.main_div r_a = 0 :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulhsu_main_selector_pin
    v r_a h_arith_table h_op

/-! ## Arith-table high-half MUL sign-witness MSB pins — `na = MSB(A)`, `nb = MSB(B)`

round 3.III sign-witness MSB pins for the signed high-half
MUL family — exact MUL-side mirrors of `arith_div_np_eq_msb_of_dividend`
/ `arith_div_nb_eq_msb_of_divisor`, with the input column re-labelling
appropriate to ArithMul (operands sit in `a[]` / `b[]` not `c[]` / `b[]`).

Per the row-type table at `arith.pil:222-234` (legend at lines 222-229):

* MULH (op = 181, signed × signed → high) — row signature
  `na = a3, nb = b3, np = c3, nr = d3`: `na` carries the MSB of the
  rs1 chunk packing (i.e. MSB of `packed4 a[0..3]`); `nb` carries the
  MSB of the rs2 chunk packing.
* MULHSU (op = 179, signed × unsigned → high) — same row signature for
  `na = a3` (rs1 is signed) but `nb` is pinned to 0 by
  `arith_table_op_mulhsu_basic_mode_pin` since rs2 is unsigned.

Trust class #6b — lookup soundness on the consumer-side
`arith_table_assumes` bus row composed with the arith_table content
(`arith.pil:286-287` + `arith_table_data.rs::ARITH_TABLE` MULH/MULHSU
rows whose flag-field bit encoding per `arith_table_helpers.rs:130-140`
binds `na`/`nb` to the MSB convention). Same trust kind as
`arith_div_np_eq_msb_of_dividend` / `arith_div_nb_eq_msb_of_divisor`,
narrower scope (ArithMul rows in place of ArithDiv rows). -/

/-! ## Arith-table MULW mode projections (op = 0xb6 = 182)

Per the row-type table at `arith.pil:222-234`, the faithful static MULW
projection pins `m32 = 1`, `div = 0`, `nr = 0`, and the sign witnesses to
zero. The old `sext = 0` claim was false as a static ROM fact; concrete
rows include both `sext = 0` and `sext = 1`.

The MULW row is **primary** lane (writes the low-32 product into the
`c[]` chunks, which the bus emits as `bus_res0`), so the selector pin
fixes `main_mul = 1, main_div = 0`.

PIL citation for the faithful static subset below: `arith.pil:286-287`
(`arith_table_assumes`) composed with the MULW=0xb6 row of
`arith_table_data.rs::ARITH_TABLE`. -/

/-- **Arith-table MULW basic mode pin (derived).**
    True static subset of the MULW rows. `sext` is intentionally not pinned
    here: concrete ROM rows include both `sext = 0` and `sext = 1`. -/
theorem arith_table_op_mulw_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_op : v.op r_a = 182) :
    v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0 ∧ v.nr r_a = 0
      ∧ v.m32 r_a = 1 ∧ v.div r_a = 0 :=
  ZiskFv.AirsClean.ArithTableProjections.Mul.mulw_basic_mode_pin
    v r_a h_arith_table h_op

end ZiskFv.Airs.Arith
