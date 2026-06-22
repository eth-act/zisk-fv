import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Arith.CarryChain

/-!
Named-column mirror of the ZisK `Arith` AIR, restricted to the
**DIV/REM subset** (clone of `Airs/Arith/Mul.lean` for RV64 DIV / DIVU
/ REM / REMU rows). After Phase F4 retirement, the structure no longer
exposes the underlying `C F ExtF` circuit or the `Circuit.main`-backed
extraction-bridge — the named columns are taken as primitive accessors,
matching the post-retirement shape of `Valid_BinaryAdd` /
`Valid_BinaryExtension` / `Valid_Mem*` after Phase D3+D4.

The Arith state machine is the same AIR used for MUL, but a single row
serves a pair of opcodes dispatched through the `div` / `main_div` /
`main_mul` selectors:

```
// arith.pil:222-234 — row-type table
// div m32 sa  sb  primary  secondary  opcodes
//  0   0   1   1  mul      mulh       0xb4 180  0xb5 181   (MUL family)
//  1   0   0   0  divu     remu       0xb8 184  0xb9 185
//  1   0   1   1  div      rem        0xba 186  0xbb 187
```

Each "DIV family" Arith row has `div = 1`. The bus-result lane is
selected per opcode:

* **DIV / DIVU (primary, `main_div = 1`, `main_mul = 0`):** bus emits
  the *quotient*, packed into the Arith column `a[0..3]`:
    * `bus_res0 = a[0] + a[1] * 2^16`
    * `bus_res1_64 = a[2] + a[3] * 2^16`
  (arith.pil:253-259 — `main_div * (a[0] + a[1] * CHUNK_SIZE)` summand).
* **REM / REMU (secondary, `main_mul = 0`, `main_div = 0` →
  `secondary = 1`):** bus emits the *remainder*, packed into the Arith
  column `d[0..3]`:
    * `bus_res0 = d[0] + d[1] * 2^16`
    * `bus_res1_64 = d[2] + d[3] * 2^16`
  (arith.pil:253-259 — `secondary * (d[0] + d[1] * CHUNK_SIZE)` summand).

The Arith column `c[]` holds the dividend (input `a`, post-renaming) on
division rows — per `bus_a0 = div * (c[0] + c[1]*CHUNK_SIZE) + (1 - div)
* (a[0] + a[1]*CHUNK_SIZE)` at arith.pil:247: on DIV rows (`div = 1`),
the bus `a` lane comes from `c[]`.

The column indices are identical to `Valid_ArithMul` (Arith is a single
schema; DIV-family rows just set different selectors).
-/

namespace ZiskFv.Airs.ArithDiv

open Goldilocks

/-- Named accessors for one row of ZisK's `Arith` AIR, restricted to the
    DIV/REM-relevant columns.

    Column layout from `ZiskFv/ZiskFv/Extraction/Arith.lean`:

    * `cy_0..cy_6` — stage-1 cols 0–6 — the 7 carry-chain witnesses
      used by `constraint_31..38_every_row`. Range-bounded by the
      `ARITH_RANGE_CARRY` lookup table (see `Airs/Arith/Ranges.lean`).
    * `a[0..3]`, `b[0..3]`, `c[0..3]`, `d[0..3]` — stage-1 cols 7–22.
      On DIV/DIVU rows (`main_div = 1`, primary) the quotient is packed
      into `a[0..3]`, the remainder into `d[0..3]`. On REM/REMU rows
      (secondary) the same layout holds — every Arith division row
      witnesses both quotient (a) and remainder (d); the Main-side
      opcode selects which pair of lanes goes on the bus.
    * `na`, `nb`, `nr`, `np`, `sext`, `m32`, `div` — stage-1 cols 23–29.
      For 64-bit DIVU/REMU all zero; for signed DIV/REM `na`, `nb`, `np`,
      `nr` follow the operand/quotient/remainder signs. `div = 1` marks
      the row as division (vs. multiplication), `m32 = 0` selects the
      64-bit width (divu_w/div_w/remu_w/rem_w out of scope).
    * `fab`, `na_fb`, `nb_fa` — stage-1 cols 30–32 — sign-consistency
      witnesses pinned by `constraint_6/7/8_every_row` to
      `1 - 2·na - 2·nb + 4·na·nb`, `na·(1-2·nb)`, `nb·(1-2·na)`.
    * `main_mul`, `main_div` — stage-1 cols 33–34. On DIV/DIVU rows
      `main_div = 1`, `main_mul = 0`; on REM/REMU rows (secondary)
      both are zero. The `secondary` row-expr (arith.pil:246) is
      `1 - main_mul - main_div`.
    * `signed`, `div_by_zero`, `div_overflow`, `range_ab`, `range_cd` —
      stage-1 cols 35–37 and 42–43 — remaining `arith_table_assumes`
      lookup columns. They are structural fields for the full 15-column
      Clean ArithTable lookup tuple; adding them does not assert any table
      membership or value pin.
    * `inv_sum_all_bs` — stage-1 col 38 — inverse witness used by
      `constraint_25_every_row` to force `div_by_zero` exactly when a division
      row has zero divisor chunks.
    * `op` — stage-1 col 39 — the 8-bit opcode literal
      (0xb8..0xbb for 64-bit DIV family).
    * `bus_res1` — stage-1 col 40 — the range-checked high-32 witness
      column. For the 64-bit div cases (sext = 0, m32 = 0) it equals
      `bus_res1_64` (see constraint 46 in `Extraction/Arith`).
    * `multiplicity` — stage-1 col 41 — operation-bus consume multiplicity. -/
structure Valid_ArithDiv (F ExtF : Type)
    [Field F] [Field ExtF] where
  cy_0 : ℕ → F
  cy_1 : ℕ → F
  cy_2 : ℕ → F
  cy_3 : ℕ → F
  cy_4 : ℕ → F
  cy_5 : ℕ → F
  cy_6 : ℕ → F
  a_0 : ℕ → F
  a_1 : ℕ → F
  a_2 : ℕ → F
  a_3 : ℕ → F
  b_0 : ℕ → F
  b_1 : ℕ → F
  b_2 : ℕ → F
  b_3 : ℕ → F
  c_0 : ℕ → F
  c_1 : ℕ → F
  c_2 : ℕ → F
  c_3 : ℕ → F
  d_0 : ℕ → F
  d_1 : ℕ → F
  d_2 : ℕ → F
  d_3 : ℕ → F
  na : ℕ → F
  nb : ℕ → F
  nr : ℕ → F
  np : ℕ → F
  sext : ℕ → F
  m32 : ℕ → F
  div : ℕ → F
  fab : ℕ → F
  na_fb : ℕ → F
  nb_fa : ℕ → F
  main_div : ℕ → F
  main_mul : ℕ → F
  signed : ℕ → F
  div_by_zero : ℕ → F
  div_overflow : ℕ → F
  inv_sum_all_bs : ℕ → F
  op : ℕ → F
  bus_res1 : ℕ → F
  multiplicity : ℕ → F
  range_ab : ℕ → F
  range_cd : ℕ → F

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- `main_mul` and `main_div` are mutually exclusive: `main_mul * main_div = 0`.
    Rewrites `constraint_2_every_row`. Same constraint as MUL rows — this
    is a global Arith-AIR boolean not specific to mode. -/
@[simp]
def main_mul_div_disjoint (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.main_mul row * v.main_div row = 0

/-- `m32` is boolean — rewrites `constraint_40_every_row`. -/
@[simp]
def boolean_m32 (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.m32 row * (1 - v.m32 row) = 0

/-- `na` is boolean — rewrites `constraint_41_every_row`. -/
@[simp]
def boolean_na (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.na row * (1 - v.na row) = 0

/-- `nb` is boolean — rewrites `constraint_42_every_row`. -/
@[simp]
def boolean_nb (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.nb row * (1 - v.nb row) = 0

/-- `nr` is boolean — rewrites `constraint_43_every_row`. -/
@[simp]
def boolean_nr (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.nr row * (1 - v.nr row) = 0

/-- `np` is boolean — rewrites `constraint_44_every_row`. -/
@[simp]
def boolean_np (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.np row * (1 - v.np row) = 0

/-- `sext` is boolean — rewrites `constraint_45_every_row`. -/
@[simp]
def boolean_sext (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.sext row * (1 - v.sext row) = 0

/-! ## Additional local constraints exposed by uncurated Arith extraction -/

/-- `div` is boolean — mirrors `constraint_39_every_row`. -/
@[simp]
def boolean_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div row * (1 - v.div row) = 0

/-! ## W-mode high-lane local constraints -/

/-- W-mode zeroes the high 32 bits of the operation-bus `a` lane — mirrors
    `constraint_47_every_row`. -/
@[simp]
def w_mode_bus_a_hi_zero (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.m32 row
    * (v.div row * (v.c_2 row + v.c_3 row * 65536)
      + (1 - v.div row) * (v.a_2 row + v.a_3 row * 65536)) = 0

/-- W-mode zeroes the high 32 bits of the operation-bus `b` lane — mirrors
    `constraint_48_every_row`. -/
@[simp]
def w_mode_bus_b_hi_zero (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.m32 row * (v.b_2 row + v.b_3 row * 65536) = 0

/-! ## Boundary-specialized local constraints

These are the named-column mirrors of the supported row-local constraints
exposed once Arith extraction no longer uses the old `--only` list. They are
kept separate from `div_row_constraints_with_c46`, because existing DIV/REM
callers consume only the carry-chain + `bus_res1` equation; boundary handling
needs these additional facts explicitly.
-/

/-- `main_div` is boolean — mirrors `constraint_0_every_row`. -/
@[simp]
def boolean_main_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.main_div row * (v.main_div row - 1) = 0

/-- `main_mul` is boolean — mirrors `constraint_1_every_row`. -/
@[simp]
def boolean_main_mul (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.main_mul row * (v.main_mul row - 1) = 0

/-- `signed` is boolean — mirrors `constraint_3_every_row`. -/
@[simp]
def boolean_signed (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.signed row * (1 - v.signed row) = 0

/-- `div_by_zero` is boolean — mirrors `constraint_4_every_row`. -/
@[simp]
def boolean_div_by_zero (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * (1 - v.div_by_zero row) = 0

/-- `div_overflow` is boolean — mirrors `constraint_5_every_row`. -/
@[simp]
def boolean_div_overflow (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (1 - v.div_overflow row) = 0

/-- If `div_by_zero` is active, divisor chunk `b[0]` is zero — mirrors
    `constraint_9_every_row`. -/
@[simp]
def div_by_zero_forces_b0 (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * v.b_0 row = 0

/-- If `div_by_zero` is active, divisor chunk `b[1]` is zero — mirrors
    `constraint_10_every_row`. -/
@[simp]
def div_by_zero_forces_b1 (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * v.b_1 row = 0

/-- If `div_by_zero` is active, divisor chunk `b[2]` is zero — mirrors
    `constraint_11_every_row`. -/
@[simp]
def div_by_zero_forces_b2 (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * v.b_2 row = 0

/-- If `div_by_zero` is active, divisor chunk `b[3]` is zero — mirrors
    `constraint_12_every_row`. -/
@[simp]
def div_by_zero_forces_b3 (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * v.b_3 row = 0

/-- Div-by-zero quotient low chunk `a[0] = 0xffff` — mirrors
    `constraint_13_every_row`. -/
@[simp]
def div_by_zero_forces_a0_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * (v.a_0 row - 65535) = 0

/-- Div-by-zero quotient low chunk `a[1] = 0xffff` — mirrors
    `constraint_14_every_row`. -/
@[simp]
def div_by_zero_forces_a1_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * (v.a_1 row - 65535) = 0

/-- Div-by-zero quotient high chunk `a[2]` — mirrors
    `constraint_15_every_row`, with W-mode high chunks zeroed. -/
@[simp]
def div_by_zero_forces_a2_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * (v.a_2 row - (1 - v.m32 row) * 65535) = 0

/-- Div-by-zero quotient high chunk `a[3]` — mirrors
    `constraint_16_every_row`, with W-mode high chunks zeroed. -/
@[simp]
def div_by_zero_forces_a3_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * (v.a_3 row - (1 - v.m32 row) * 65535) = 0

/-- Overflow divisor chunk `b[0] = 0xffff` — mirrors
    `constraint_17_every_row`. -/
@[simp]
def div_overflow_forces_b0_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (v.b_0 row - 65535) = 0

/-- Overflow divisor chunk `b[1] = 0xffff` — mirrors
    `constraint_18_every_row`. -/
@[simp]
def div_overflow_forces_b1_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (v.b_1 row - 65535) = 0

/-- Overflow divisor high chunk `b[2]` — mirrors `constraint_19_every_row`. -/
@[simp]
def div_overflow_forces_b2_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (v.b_2 row - (1 - v.m32 row) * 65535) = 0

/-- Overflow divisor high chunk `b[3]` — mirrors `constraint_20_every_row`. -/
@[simp]
def div_overflow_forces_b3_ffff (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (v.b_3 row - (1 - v.m32 row) * 65535) = 0

/-- Overflow dividend chunk `c[0] = 0` — mirrors `constraint_21_every_row`. -/
@[simp]
def div_overflow_forces_c0_zero (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * v.c_0 row = 0

/-- Overflow dividend chunk `c[1]` — mirrors `constraint_22_every_row`. -/
@[simp]
def div_overflow_forces_c1_intmin (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (v.c_1 row - v.m32 row * 32768) = 0

/-- Overflow dividend chunk `c[2] = 0` — mirrors `constraint_23_every_row`. -/
@[simp]
def div_overflow_forces_c2_zero (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * v.c_2 row = 0

/-- Overflow dividend chunk `c[3]` — mirrors `constraint_24_every_row`. -/
@[simp]
def div_overflow_forces_c3_intmin (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (v.c_3 row - (1 - v.m32 row) * 32768) = 0

/-- Inverse-sum div-by-zero detector — mirrors `constraint_25_every_row`. -/
@[simp]
def div_by_zero_inverse_sum (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  (v.div row - v.div_by_zero row)
    * (1 - v.inv_sum_all_bs row
      * (((v.b_0 row + v.b_1 row) + v.b_2 row) + v.b_3 row)) = 0

/-- `div_by_zero` is active only on division rows — mirrors
    `constraint_26_every_row`. -/
@[simp]
def div_by_zero_only_on_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * (1 - v.div row) = 0

/-- `div_overflow` is active only on division rows — mirrors
    `constraint_27_every_row`. -/
@[simp]
def div_overflow_only_on_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (1 - v.div row) = 0

/-- `div_overflow` is active only on signed rows — mirrors
    `constraint_28_every_row`. -/
@[simp]
def div_overflow_only_on_signed (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * (1 - v.signed row) = 0

/-- Overflow and div-by-zero are mutually exclusive — mirrors
    `constraint_29_every_row`. -/
@[simp]
def div_overflow_div_by_zero_disjoint (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_overflow row * v.div_by_zero row = 0

/-- Div-by-zero and overflow are mutually exclusive — mirrors
    `constraint_30_every_row`. -/
@[simp]
def div_by_zero_div_overflow_disjoint (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.div_by_zero row * v.div_overflow row = 0

/-- Boundary-local ArithDiv constraints newly exposed by uncurated Arith
    extraction. This deliberately excludes lookup/bus/range constraints
    `49..64`, which remain modeled by the existing operation-bus and lookup
    witnesses. -/
@[simp]
def div_boundary_constraints (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  boolean_main_div v row
  ∧ boolean_main_mul v row
  ∧ boolean_signed v row
  ∧ boolean_div_by_zero v row
  ∧ boolean_div_overflow v row
  ∧ div_by_zero_forces_b0 v row
  ∧ div_by_zero_forces_b1 v row
  ∧ div_by_zero_forces_b2 v row
  ∧ div_by_zero_forces_b3 v row
  ∧ div_by_zero_forces_a0_ffff v row
  ∧ div_by_zero_forces_a1_ffff v row
  ∧ div_by_zero_forces_a2_ffff v row
  ∧ div_by_zero_forces_a3_ffff v row
  ∧ div_overflow_forces_b0_ffff v row
  ∧ div_overflow_forces_b1_ffff v row
  ∧ div_overflow_forces_b2_ffff v row
  ∧ div_overflow_forces_b3_ffff v row
  ∧ div_overflow_forces_c0_zero v row
  ∧ div_overflow_forces_c1_intmin v row
  ∧ div_overflow_forces_c2_zero v row
  ∧ div_overflow_forces_c3_intmin v row
  ∧ div_by_zero_inverse_sum v row
  ∧ div_by_zero_only_on_div v row
  ∧ div_overflow_only_on_div v row
  ∧ div_overflow_only_on_signed v row
  ∧ div_overflow_div_by_zero_disjoint v row
  ∧ div_by_zero_div_overflow_disjoint v row

/-- All supported row-local ArithDiv constraints that were absent from the old
    `--only` extraction list. Lookup, permutation, and challenge/exposed
    constraints remain modeled separately. -/
@[simp]
def div_previously_omitted_local_constraints
    (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  div_boundary_constraints v row
  ∧ boolean_div v row
  ∧ w_mode_bus_a_hi_zero v row
  ∧ w_mode_bus_b_hi_zero v row

/-! ## Boundary equation projections -/

theorem b0_eq_zero_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_b0 v row) (h_flag : v.div_by_zero row = 1) :
    v.b_0 row = 0 := by
  unfold div_by_zero_forces_b0 at h
  rw [h_flag] at h
  simpa using h

theorem b1_eq_zero_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_b1 v row) (h_flag : v.div_by_zero row = 1) :
    v.b_1 row = 0 := by
  unfold div_by_zero_forces_b1 at h
  rw [h_flag] at h
  simpa using h

theorem b2_eq_zero_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_b2 v row) (h_flag : v.div_by_zero row = 1) :
    v.b_2 row = 0 := by
  unfold div_by_zero_forces_b2 at h
  rw [h_flag] at h
  simpa using h

theorem b3_eq_zero_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_b3 v row) (h_flag : v.div_by_zero row = 1) :
    v.b_3 row = 0 := by
  unfold div_by_zero_forces_b3 at h
  rw [h_flag] at h
  simpa using h

theorem div_by_zero_eq_one_of_zero_b_chunks
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_inverse_sum v row)
    (h_div : v.div row = 1)
    (h_b0 : v.b_0 row = 0) (h_b1 : v.b_1 row = 0)
    (h_b2 : v.b_2 row = 0) (h_b3 : v.b_3 row = 0) :
    v.div_by_zero row = 1 := by
  unfold div_by_zero_inverse_sum at h
  rw [h_div, h_b0, h_b1, h_b2, h_b3] at h
  have h_sub : 1 - v.div_by_zero row = 0 := by
    simpa using h
  exact (sub_eq_zero.mp h_sub).symm

theorem a0_eq_ffff_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_a0_ffff v row) (h_flag : v.div_by_zero row = 1) :
    v.a_0 row = 65535 := by
  unfold div_by_zero_forces_a0_ffff at h
  rw [h_flag] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem a1_eq_ffff_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_a1_ffff v row) (h_flag : v.div_by_zero row = 1) :
    v.a_1 row = 65535 := by
  unfold div_by_zero_forces_a1_ffff at h
  rw [h_flag] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem a2_eq_ffff_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_a2_ffff v row)
    (h_flag : v.div_by_zero row = 1) (h_m32 : v.m32 row = 0) :
    v.a_2 row = 65535 := by
  unfold div_by_zero_forces_a2_ffff at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem a3_eq_ffff_of_div_by_zero
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_by_zero_forces_a3_ffff v row)
    (h_flag : v.div_by_zero row = 1) (h_m32 : v.m32 row = 0) :
    v.a_3 row = 65535 := by
  unfold div_by_zero_forces_a3_ffff at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem b0_eq_ffff_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_b0_ffff v row) (h_flag : v.div_overflow row = 1) :
    v.b_0 row = 65535 := by
  unfold div_overflow_forces_b0_ffff at h
  rw [h_flag] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem b1_eq_ffff_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_b1_ffff v row) (h_flag : v.div_overflow row = 1) :
    v.b_1 row = 65535 := by
  unfold div_overflow_forces_b1_ffff at h
  rw [h_flag] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem b2_eq_ffff_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_b2_ffff v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 0) :
    v.b_2 row = 65535 := by
  unfold div_overflow_forces_b2_ffff at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem b2_eq_zero_of_div_overflow_w
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_b2_ffff v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 1) :
    v.b_2 row = 0 := by
  unfold div_overflow_forces_b2_ffff at h
  rw [h_flag, h_m32] at h
  simpa using h

theorem b3_eq_ffff_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_b3_ffff v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 0) :
    v.b_3 row = 65535 := by
  unfold div_overflow_forces_b3_ffff at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem b3_eq_zero_of_div_overflow_w
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_b3_ffff v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 1) :
    v.b_3 row = 0 := by
  unfold div_overflow_forces_b3_ffff at h
  rw [h_flag, h_m32] at h
  simpa using h

theorem c0_eq_zero_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_c0_zero v row) (h_flag : v.div_overflow row = 1) :
    v.c_0 row = 0 := by
  unfold div_overflow_forces_c0_zero at h
  rw [h_flag] at h
  simpa using h

theorem c1_eq_zero_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_c1_intmin v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 0) :
    v.c_1 row = 0 := by
  unfold div_overflow_forces_c1_intmin at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem c1_eq_intmin_of_div_overflow_w
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_c1_intmin v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 1) :
    v.c_1 row = 32768 := by
  unfold div_overflow_forces_c1_intmin at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem c2_eq_zero_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_c2_zero v row) (h_flag : v.div_overflow row = 1) :
    v.c_2 row = 0 := by
  unfold div_overflow_forces_c2_zero at h
  rw [h_flag] at h
  simpa using h

theorem c3_eq_intmin_of_div_overflow
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_c3_intmin v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 0) :
    v.c_3 row = 32768 := by
  unfold div_overflow_forces_c3_intmin at h
  rw [h_flag, h_m32] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem c3_eq_zero_of_div_overflow_w
    {v : Valid_ArithDiv F ExtF} {row : ℕ}
    (h : div_overflow_forces_c3_intmin v row)
    (h_flag : v.div_overflow row = 1) (h_m32 : v.m32 row = 1) :
    v.c_3 row = 0 := by
  unfold div_overflow_forces_c3_intmin at h
  rw [h_flag, h_m32] at h
  simpa using h

/-- **DIV/REM-subset mode predicates bundled.** Same boolean-selector
    subset the MUL-family compositional proof relies on — these
    constraints are AIR-global, not mode-specific. The carry-chain
    constraints (31–38), specialized to `div = 1`, remain reachable
    via the raw extraction bridges. -/
@[simp]
def div_mode_booleans (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  main_mul_div_disjoint v row
  ∧ boolean_m32 v row
  ∧ boolean_na v row
  ∧ boolean_nb v row
  ∧ boolean_nr v row
  ∧ boolean_np v row
  ∧ boolean_sext v row

section BusEmission

open ZiskFv.Airs.OperationBus

/-- Arith's operation-bus emission for a DIV-family row, selected by
    primary (`main_div = 1`) vs. secondary (`secondary = 1`) mode.

    Mirrors the `proves_operation(op:, a:, b:, c:, flag:, mul:)` call at
    `zisk/state-machines/arith/pil/arith.pil:269-270`. The bus
    `a` / `b` / `c` lanes project through:

    * `bus_a0` = `div * (c[0] + c[1] * 2^16) + (1 - div) * (a[0] + a[1] * 2^16)`
      (arith.pil:247); on DIV rows (`div = 1`) this is `c[0] + c[1] * 2^16`.
    * `bus_a1` = `div * (c[2] + c[3] * 2^16) + (1 - div) * (a[2] + a[3] * 2^16)`
      (arith.pil:248); on DIV rows `c[2] + c[3] * 2^16`.
    * `bus_b0` / `bus_b1` = `b[0] + b[1]*2^16` / `b[2] + b[3]*2^16`
      (arith.pil:250-251); same as MUL.
    * `bus_res0` = `secondary * (d[0] + d[1]*2^16) + main_mul * (c[0] + c[1]*2^16)
                  + main_div * (a[0] + a[1]*2^16)` (arith.pil:253-255).
      For primary DIV/DIVU (`main_div = 1`) this is `a[0] + a[1]*2^16`
      (the quotient low lane); for secondary REM/REMU (both mains 0,
      `secondary = 1`) this is `d[0] + d[1]*2^16` (the remainder low lane).
    * `bus_res1_64` similarly (arith.pil:257-259) selects `a[2] + a[3]*2^16`
      for DIV/DIVU and `d[2] + d[3]*2^16` for REM/REMU; `bus_res1` is the
      range-checked 32-bit witness column pinned via constraint 46 on the
      64-bit case (sext = 0, m32 = 0) to `bus_res1_64`.

    Since the bus-result projection is selector-dependent, we
    parameterize this over two separate builders — one for primary
    DIV/DIVU (quotient = `a[]`), one for secondary REM/REMU
    (remainder = `d[]`). The bus-row Lean structure is the same
    `OperationBusEntry`; only which Arith columns flow into `c_lo` /
    `c_hi` differs.

    On DIV rows we also have `flag = div_by_zero`; for our compositional
    archetype this sits as a free field on the bus entry. We leave
    `flag = 0` here, matching the semantics that a non-div-by-zero
    divide emits `flag = 0` and the Sail side never observes the flag
    directly; div-by-zero is handled by the PIL + arith_table
    assumption network. -/
@[simp]
def opBus_row_ArithDiv {F ExtF : Type} [Field F] [Field ExtF]
    (v : Valid_ArithDiv F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.multiplicity row
    op := v.op row
    -- DIV rows: `div = 1` → bus `a` comes from `c[]`.
    a_lo := v.c_0 row + v.c_1 row * 65536
    a_hi := v.c_2 row + v.c_3 row * 65536
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
    -- Quotient output lane: `a[0] + a[1] * 2^16` on main_div = 1.
    c_lo := v.a_0 row + v.a_1 row * 65536
    c_hi := v.bus_res1 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Arith's operation-bus emission for a DIV-family row in **secondary**
    mode (REM / REMU). On secondary rows `main_mul = 0`, `main_div = 0`,
    so `secondary = 1` and the bus `c` lane comes from `d[]` — the
    remainder output.

    Same row-level layout as `opBus_row_ArithDiv` except the result lane
    is packed from `d[0..3]` rather than `a[0..3]`. -/
@[simp]
def opBus_row_ArithDivSecondary {F ExtF : Type} [Field F] [Field ExtF]
    (v : Valid_ArithDiv F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.multiplicity row
    op := v.op row
    -- DIV rows: `div = 1` → bus `a` comes from `c[]`.
    a_lo := v.c_0 row + v.c_1 row * 65536
    a_hi := v.c_2 row + v.c_3 row * 65536
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
    -- Remainder output lane: `d[0] + d[1] * 2^16` on secondary = 1.
    c_lo := v.d_0 row + v.d_1 row * 65536
    c_hi := v.bus_res1 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- ArithDiv's operation-bus **consumer** row for the remainder-bound
    comparison.

    Mirrors the `assumes_operation(...)` call at
    `zisk/state-machines/arith/pil/arith.pil:274-277`. On unsigned
    64-bit DIVU/REMU rows (`nr = nb = m32 = 0`, `div = 1`,
    `div_by_zero = 0`) this simplifies to an `OP_LTU` comparison between
    the remainder chunks `d[0..3]` and divisor chunks `b[0..3]`, with
    output `c = [1, 0]` and `flag = 1`.

    The opcode literals are the Binary-table op ids:
    `OP_LTU = 6`, `OP_LT_ABS_NP = 80`, `OP_LT_ABS_PN = 81`,
    `OP_GT = 8`. -/
@[simp]
def opBus_row_ArithDivRemainderBound {F ExtF : Type} [Field F] [Field ExtF]
    (v : Valid_ArithDiv F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.div row * (1 - v.div_by_zero row)
    op := (1 - v.nr row) * (1 - v.nb row) * 6
        + v.nr row * (1 - v.nb row) * 80
        + (1 - v.nr row) * v.nb row * 81
        + v.nr row * v.nb row * 8
    a_lo := v.d_0 row + v.d_1 row * 65536
    a_hi := v.d_2 row + v.d_3 row * 65536
        + v.m32 row * v.nr row * 4294967295
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
        + v.m32 row * v.nb row * 4294967295
    c_lo := 1
    c_hi := 0
    flag := 1
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

end BusEmission

/-!
## Carry-chain specialization (DIV-unsigned)

Post-Phase-F4-retirement, the carry-chain bundle is expressed entirely
over named columns — no `Circuit.main` / `v.circuit` references. Each
`carry_eq_*_div` predicate captures the named-column form of the
corresponding `Extraction.Arith.constraint_3{1..8}_every_row` /
`constraint_{6,7,8}_every_row`; the `bus_res1_eq` predicate captures
constraint 46. The packed identity

    a_packed * b_packed + d_packed = c_packed

for the DIVU/REMU mode (`fab = 1`,
`na = nb = np = nr = sext = m32 = 0`, `div = 1`) is derived from
these named-form predicates exactly as the pre-retirement version
derived from the `Circuit.main`-form constraint predicates. Here `a`
holds the quotient, `b` the divisor, `c` the dividend, `d` the
remainder.
-/

section CarryChain

open ZiskFv.Airs.ArithCarryChain

/-- Named-form `fab` closure equation — mirrors `constraint_6_every_row`. -/
@[simp]
def fab_eq_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row - ((1 - 2 * v.na row) - 2 * v.nb row + 4 * v.na row * v.nb row) = 0

/-- Named-form `na_fb` closure equation — mirrors `constraint_7_every_row`. -/
@[simp]
def na_fb_eq_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.na_fb row - (v.na row * (1 - 2 * v.nb row)) = 0

/-- Named-form `nb_fa` closure equation — mirrors `constraint_8_every_row`. -/
@[simp]
def nb_fa_eq_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.nb_fa row - (v.nb row * (1 - 2 * v.na row)) = 0

/-- Named-form carry equation 0 — mirrors `constraint_31_every_row`.
    The original `Circuit.main`-form was:
    `(fab*a0*b0 - c0 + 2*np*c0 + div*d0 - 2*nr*d0 - cy_0 * 65536) = 0` -/
@[simp]
def carry_eq_0_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_0 row * v.b_0 row - v.c_0 row + 2 * v.np row * v.c_0 row
    + v.div row * v.d_0 row - 2 * v.nr row * v.d_0 row
    - v.cy_0 row * 65536 = 0

/-- Named-form carry equation 1 — mirrors `constraint_32_every_row`. -/
@[simp]
def carry_eq_1_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_1 row * v.b_0 row + v.fab row * v.a_0 row * v.b_1 row
    - v.c_1 row + 2 * v.np row * v.c_1 row
    + v.div row * v.d_1 row - 2 * v.nr row * v.d_1 row
    + v.cy_0 row - v.cy_1 row * 65536 = 0

/-- Named-form carry equation 2 — mirrors `constraint_33_every_row`. -/
@[simp]
def carry_eq_2_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_2 row * v.b_0 row + v.fab row * v.a_1 row * v.b_1 row
    + v.fab row * v.a_0 row * v.b_2 row
    + v.a_0 row * v.nb_fa row * v.m32 row
    + v.b_0 row * v.na_fb row * v.m32 row
    - v.c_2 row + 2 * v.np row * v.c_2 row
    + v.div row * v.d_2 row - 2 * v.nr row * v.d_2 row
    - v.np row * v.div row * v.m32 row + v.nr row * v.m32 row
    + v.cy_1 row - v.cy_2 row * 65536 = 0

/-- Named-form carry equation 3 — mirrors `constraint_34_every_row`. -/
@[simp]
def carry_eq_3_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_0 row + v.fab row * v.a_2 row * v.b_1 row
    + v.fab row * v.a_1 row * v.b_2 row + v.fab row * v.a_0 row * v.b_3 row
    + v.a_1 row * v.nb_fa row * v.m32 row
    + v.b_1 row * v.na_fb row * v.m32 row
    - v.c_3 row + 2 * v.np row * v.c_3 row
    + v.div row * v.d_3 row - 2 * v.nr row * v.d_3 row
    + v.cy_2 row - v.cy_3 row * 65536 = 0

/-- Named-form carry equation 4 — mirrors `constraint_35_every_row`. -/
@[simp]
def carry_eq_4_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_1 row + v.fab row * v.a_2 row * v.b_2 row
    + v.fab row * v.a_1 row * v.b_3 row
    + v.na row * v.nb row * v.m32 row
    + v.b_0 row * v.na_fb row * (1 - v.m32 row)
    + v.a_0 row * v.nb_fa row * (1 - v.m32 row)
    - v.np row * v.m32 row * (1 - v.div row)
    - v.np row * (1 - v.m32 row) * v.div row
    + v.nr row * (1 - v.m32 row)
    - v.d_0 row * (1 - v.div row)
    + 2 * v.np row * v.d_0 row * (1 - v.div row)
    + v.cy_3 row - v.cy_4 row * 65536 = 0

/-- Named-form carry equation 5 — mirrors `constraint_36_every_row`. -/
@[simp]
def carry_eq_5_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_2 row + v.fab row * v.a_2 row * v.b_3 row
    + v.a_1 row * v.nb_fa row * (1 - v.m32 row)
    + v.b_1 row * v.na_fb row * (1 - v.m32 row)
    - v.d_1 row * (1 - v.div row)
    + v.d_1 row * 2 * v.np row * (1 - v.div row)
    + v.cy_4 row - v.cy_5 row * 65536 = 0

/-- Named-form carry equation 6 — mirrors `constraint_37_every_row`. -/
@[simp]
def carry_eq_6_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_3 row
    + v.a_2 row * v.nb_fa row * (1 - v.m32 row)
    + v.b_2 row * v.na_fb row * (1 - v.m32 row)
    - v.d_2 row * (1 - v.div row)
    + 2 * v.np row * v.d_2 row * (1 - v.div row)
    + v.cy_5 row - v.cy_6 row * 65536 = 0

/-- Named-form carry equation 7 — mirrors `constraint_38_every_row`. -/
@[simp]
def carry_eq_7_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  65536 * v.na row * v.nb row * (1 - v.m32 row)
    + v.a_3 row * v.nb_fa row * (1 - v.m32 row)
    + v.b_3 row * v.na_fb row * (1 - v.m32 row)
    - 65536 * v.np row * (1 - v.div row) * (1 - v.m32 row)
    - v.d_3 row * (1 - v.div row)
    + 2 * v.np row * v.d_3 row * (1 - v.div row)
    + v.cy_6 row = 0

/-- Named-form bus_res1 equation — mirrors `constraint_46_every_row`. -/
@[simp]
def bus_res1_eq_div (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  v.bus_res1 row -
    (v.sext row * 4294967295
      + (1 - v.m32 row)
        * (((1 - v.main_mul row - v.main_div row)
            * (v.d_2 row + v.d_3 row * 65536))
          + (v.main_mul row * (v.c_2 row + v.c_3 row * 65536))
          + (v.main_div row * (v.a_2 row + v.a_3 row * 65536)))) = 0

/-- **Bundled Arith DIV-mode carry-chain constraints.** Packs the 11
    named-form constraints the `arith_div_unsigned_packed_correct`
    theorem consumes: the 3 `fab`/`na_fb`/`nb_fa` closures + the 8
    carry equations. -/
@[simp]
def div_carry_chain_holds (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  fab_eq_div v row
  ∧ na_fb_eq_div v row
  ∧ nb_fa_eq_div v row
  ∧ carry_eq_0_div v row
  ∧ carry_eq_1_div v row
  ∧ carry_eq_2_div v row
  ∧ carry_eq_3_div v row
  ∧ carry_eq_4_div v row
  ∧ carry_eq_5_div v row
  ∧ carry_eq_6_div v row
  ∧ carry_eq_7_div v row

/-- **Extended Arith DIV-mode row constraints — includes bus_res1 equation.**
    Same shape as `div_carry_chain_holds` but additionally pins
    `bus_res1_eq_div` (the named-form analog of `constraint_46_every_row`
    at `arith.pil:263`). Required by `equiv_DIV` to discharge
    the hi-lane byte-pack equation via `div_bus_res1_eq_a_hi`
    (`Airs/Arith/BusRes1.lean`). Compliance.lean's downstream caller
    will collapse this into the universal `∀ r, arith_div_row_well_formed`
    parameter. -/
@[simp]
def div_row_constraints_with_c46 (v : Valid_ArithDiv F ExtF) (row : ℕ) : Prop :=
  div_carry_chain_holds v row
  ∧ bus_res1_eq_div v row

/-- Project out the carry-chain bundle from the extended bundle. -/
lemma div_carry_chain_holds_of_extended
    (v : Valid_ArithDiv F ExtF) (row : ℕ)
    (h : div_row_constraints_with_c46 v row) :
    div_carry_chain_holds v row := h.1

/-- Project out the bus_res1 equation from the extended bundle. -/
lemma bus_res1_eq_div_of_extended
    (v : Valid_ArithDiv F ExtF) (row : ℕ)
    (h : div_row_constraints_with_c46 v row) :
    bus_res1_eq_div v row := h.2

/-- Packed `a` over Div columns: `a[0] + a[1]*2^16 + a[2]*2^32 + a[3]*2^48`.
    For DIVU/DIV this is the quotient; for REMU/REM the quotient lane is
    still computed but unused by the bus emission. -/
@[simp]
def a_chunks_packed_div (v : Valid_ArithDiv F ExtF) (r : ℕ) : F :=
  v.a_0 r + v.a_1 r * 65536 + v.a_2 r * (65536 * 65536)
    + v.a_3 r * (65536 * 65536 * 65536)

/-- Packed `b` over Div columns: divisor. -/
@[simp]
def b_chunks_packed_div (v : Valid_ArithDiv F ExtF) (r : ℕ) : F :=
  v.b_0 r + v.b_1 r * 65536 + v.b_2 r * (65536 * 65536)
    + v.b_3 r * (65536 * 65536 * 65536)

/-- Packed `c` over Div columns: dividend. -/
@[simp]
def c_chunks_packed_div (v : Valid_ArithDiv F ExtF) (r : ℕ) : F :=
  v.c_0 r + v.c_1 r * 65536 + v.c_2 r * (65536 * 65536)
    + v.c_3 r * (65536 * 65536 * 65536)

/-- Packed `d` over Div columns: remainder. -/
@[simp]
def d_chunks_packed_div (v : Valid_ArithDiv F ExtF) (r : ℕ) : F :=
  v.d_0 r + v.d_1 r * 65536 + v.d_2 r * (65536 * 65536)
    + v.d_3 r * (65536 * 65536 * 65536)

/-- **DIV-unsigned carry-chain specialization.**

    Named-form analog of the pre-retirement
    `arith_div_unsigned_packed_correct`. Consumes the 11 named-form
    constraint equations plus the unsigned-mode pins; concludes the
    packed identity

        a_packed * b_packed + d_packed = c_packed

    (quotient × divisor + remainder = dividend). -/
lemma arith_div_unsigned_packed_correct
    (v : Valid_ArithDiv F ExtF) (row : ℕ)
    (h6 : fab_eq_div v row)
    (h7 : na_fb_eq_div v row)
    (h8 : nb_fa_eq_div v row)
    (h31 : carry_eq_0_div v row)
    (h32 : carry_eq_1_div v row)
    (h33 : carry_eq_2_div v row)
    (h34 : carry_eq_3_div v row)
    (h35 : carry_eq_4_div v row)
    (h36 : carry_eq_5_div v row)
    (h37 : carry_eq_6_div v row)
    (h38 : carry_eq_7_div v row)
    (h_na : v.na row = 0) (h_nb : v.nb row = 0)
    (h_np : v.np row = 0) (h_nr : v.nr row = 0)
    (_h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 1) :
    a_chunks_packed_div v row * b_chunks_packed_div v row
      + d_chunks_packed_div v row
      = c_chunks_packed_div v row := by
  simp only [fab_eq_div, na_fb_eq_div, nb_fa_eq_div] at h6 h7 h8
  simp only [h_na, h_nb] at h6 h7 h8
  have h_fab : v.fab row = (1 : F) := by linear_combination h6
  have h_nafb : v.na_fb row = (0 : F) := by linear_combination h7
  have h_nbfa : v.nb_fa row = (0 : F) := by linear_combination h8
  simp only [carry_eq_0_div, carry_eq_1_div, carry_eq_2_div,
             carry_eq_3_div, carry_eq_4_div, carry_eq_5_div,
             carry_eq_6_div, carry_eq_7_div] at h31 h32 h33 h34 h35 h36 h37 h38
  simp only [h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero,
             mul_one, one_mul, sub_self]
    at h31 h32 h33 h34 h35 h36 h37 h38
  unfold a_chunks_packed_div b_chunks_packed_div c_chunks_packed_div d_chunks_packed_div
  linear_combination
    h31
    + 65536 * h32
    + (65536 * 65536) * h33
    + (65536 * 65536 * 65536) * h34
    + (65536 * 65536 * 65536 * 65536) * h35
    + (65536 * 65536 * 65536 * 65536 * 65536) * h36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h38

/-- **DIV-signed carry-chain specialization.**

    Named-form analog of the pre-retirement
    `arith_div_signed_packed_correct`. Consumes the 11 named-form
    constraint equations plus the signed-mode pins (`sext`, `m32`,
    `div`); concludes the polynomial identity

        fab * a_packed * b_packed + (1 - 2*nr) * d_packed
          + (nb_fa * a_packed + na_fb * b_packed) * B^4
          + (nr - np) * B^4 + na*nb * B^8
        = (1 - 2*np) * c_packed.

    Specializing `(na, nb, np, nr) = (0, 0, 0, 0)` recovers the
    unsigned form. -/
lemma arith_div_signed_packed_correct
    (v : Valid_ArithDiv F ExtF) (row : ℕ)
    (h6 : fab_eq_div v row)
    (h7 : na_fb_eq_div v row)
    (h8 : nb_fa_eq_div v row)
    (h31 : carry_eq_0_div v row)
    (h32 : carry_eq_1_div v row)
    (h33 : carry_eq_2_div v row)
    (h34 : carry_eq_3_div v row)
    (h35 : carry_eq_4_div v row)
    (h36 : carry_eq_5_div v row)
    (h37 : carry_eq_6_div v row)
    (h38 : carry_eq_7_div v row)
    (_h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 1) :
    (1 - 2 * v.na row - 2 * v.nb row + 4 * v.na row * v.nb row)
        * a_chunks_packed_div v row * b_chunks_packed_div v row
      + (1 - 2 * v.nr row) * d_chunks_packed_div v row
      + (v.nb row * (1 - 2 * v.na row) * a_chunks_packed_div v row
          + v.na row * (1 - 2 * v.nb row) * b_chunks_packed_div v row)
          * (65536 * 65536 * 65536 * 65536)
      + (v.nr row - v.np row) * (65536 * 65536 * 65536 * 65536)
      + v.na row * v.nb row
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np row) * c_chunks_packed_div v row := by
  simp only [fab_eq_div, na_fb_eq_div, nb_fa_eq_div] at h6 h7 h8
  have h_fab : v.fab row
    = 1 - 2 * v.na row - 2 * v.nb row + 4 * v.na row * v.nb row := by linear_combination h6
  have h_nafb : v.na_fb row
    = v.na row * (1 - 2 * v.nb row) := by linear_combination h7
  have h_nbfa : v.nb_fa row
    = v.nb row * (1 - 2 * v.na row) := by linear_combination h8
  simp only [carry_eq_0_div, carry_eq_1_div, carry_eq_2_div,
             carry_eq_3_div, carry_eq_4_div, carry_eq_5_div,
             carry_eq_6_div, carry_eq_7_div] at h31 h32 h33 h34 h35 h36 h37 h38
  simp only [h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, add_zero, sub_zero,
             mul_one, sub_self]
    at h31 h32 h33 h34 h35 h36 h37 h38
  unfold a_chunks_packed_div b_chunks_packed_div c_chunks_packed_div d_chunks_packed_div
  linear_combination
    h31
    + 65536 * h32
    + (65536 * 65536) * h33
    + (65536 * 65536 * 65536) * h34
    + (65536 * 65536 * 65536 * 65536) * h35
    + (65536 * 65536 * 65536 * 65536 * 65536) * h36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h38

/-- **DIV-unsigned carry-chain specialization (bundled form).** -/
lemma arith_div_unsigned_packed_correct_bundled
    (v : Valid_ArithDiv F ExtF) (row : ℕ)
    (h_chain : div_carry_chain_holds v row)
    (h_na : v.na row = 0) (h_nb : v.nb row = 0)
    (h_np : v.np row = 0) (h_nr : v.nr row = 0)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 1) :
    a_chunks_packed_div v row * b_chunks_packed_div v row
      + d_chunks_packed_div v row
      = c_chunks_packed_div v row := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact arith_div_unsigned_packed_correct v row h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_na h_nb h_np h_nr h_sext h_m32 h_div

/-- **DIV-signed carry-chain specialization (bundled form).** Same as
    `arith_div_signed_packed_correct` but consuming the bundled
    `div_carry_chain_holds` predicate. Used by the bridge
    `div_signed_chain_witnesses` to extract per-chunk identities over
    named columns for downstream consumption by the signed ℤ
    aggregator. -/
lemma arith_div_signed_packed_correct_bundled
    (v : Valid_ArithDiv F ExtF) (row : ℕ)
    (h_chain : div_carry_chain_holds v row)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 1) :
    (1 - 2 * v.na row - 2 * v.nb row + 4 * v.na row * v.nb row)
        * a_chunks_packed_div v row * b_chunks_packed_div v row
      + (1 - 2 * v.nr row) * d_chunks_packed_div v row
      + (v.nb row * (1 - 2 * v.na row) * a_chunks_packed_div v row
          + v.na row * (1 - 2 * v.nb row) * b_chunks_packed_div v row)
          * (65536 * 65536 * 65536 * 65536)
      + (v.nr row - v.np row) * (65536 * 65536 * 65536 * 65536)
      + v.na row * v.nb row
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np row) * c_chunks_packed_div v row := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact arith_div_signed_packed_correct v row h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_sext h_m32 h_div

end CarryChain

end ZiskFv.Airs.ArithDiv
