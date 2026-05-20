import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Arith.CarryChain

/-!
Named-column mirror of the ZisK `Arith` AIR, restricted to the MUL subset.

The Arith state machine is the multiplier behind the RV64 MUL/MULH family
(PIL: `zisk/state-machines/arith/pil/arith.pil`). It carries 65
constraints spanning 8-chunk carry chains for full 64×64 multiply-divide,
sign-extension witnesses, and the arith_table / arith_range_table lookups.

After the OpenVM Circuit retirement (Phase F3), `Valid_ArithMul` is a
plain named-column record. The previous `circuit` and `_def` fields
that tied the named accessors to the extraction's `Circuit.main` form
have been removed; structural-unpacking added 10 new named accessors
(`cy_0..cy_6` for carry witnesses + `fab`, `na_fb`, `nb_fa` for sign
products). Constraint predicates (`mul_constraint_N_named`) are
algebraic identities over the named accessors that mirror the
extraction's `Arith.extraction.constraint_N_every_row`. The canonical
AIR view is the Clean `Air.Flat.Component` at
`ZiskFv/AirsClean/ArithMul/`.
-/

namespace ZiskFv.Airs.ArithMul

open Goldilocks

/-- Named accessors for one row of ZisK's `Arith` AIR, restricted to the
    MUL-relevant columns.

    Column layout from the witness-column header in
    `ZiskFv/ZiskFv/Extraction/Arith.lean`:

    * `a[0..3]`, `b[0..3]`, `c[0..3]`, `d[0..3]` — stage-1 cols 7–22 — the
      four 16-bit chunks of each 64-bit operand and each 64-bit result lane.
      On MUL the low 64 bits of `a * b` are packed into `c[0..3]`, the high
      64 bits into `d[0..3]` (selected via `main_mul` vs. `main_div`).
    * `na`, `nb`, `nr`, `np`, `sext`, `m32`, `div` — stage-1 cols 23–29 —
      sign/mode selectors. On unsigned MUL (`mulu`/`muluh`, opcodes 0xb0/0xb1)
      all are zero; on signed MUL (`mul`/`mulh`) `na`, `nb`, `np` follow the
      operand/result signs.
    * `main_mul`, `main_div` — stage-1 cols 33–34 — dual-use selectors. On
      MUL rows `main_mul = 1` and `main_div = 0`; on DIV rows the opposite.
    * `op` — stage-1 col 39 — the 8-bit opcode literal (0xb0..0xb6 for MUL).
    * `multiplicity` — stage-1 col 41 — operation-bus consume multiplicity
      (the `mul` argument of `proves_operation` in the PIL). -/
structure Valid_ArithMul (F ExtF : Type)
    [Field F] [Field ExtF] where
  /-- Carry-chain witnesses (Arith cols 0..6). The 7 carry columns
      of the 8-chunk MUL carry-chain, in `[-0xEFFFF..0xF0000]`
      (signed) or `[0, 2^17)` (unsigned). -/
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
  /-- `fab = (1 - 2·na) - 2·nb + 4·na·nb` (Arith col 30, constraint 6).
      PIL: `zisk/state-machines/arith/pil/arith.pil:58`. Structural-
      unpacking accessor added in Phase F3 to close the schema gap
      where the carry-chain proofs accessed col 30 positionally. -/
  fab : ℕ → F
  /-- `na_fb = na · (1 - 2·nb)` (Arith col 31, constraint 7).
      PIL: `zisk/state-machines/arith/pil/arith.pil:59`. Structural-
      unpacking accessor added in Phase F3. -/
  na_fb : ℕ → F
  /-- `nb_fa = nb · (1 - 2·na)` (Arith col 32, constraint 8).
      PIL: `zisk/state-machines/arith/pil/arith.pil:60`. Structural-
      unpacking accessor added in Phase F3. -/
  nb_fa : ℕ → F
  main_div : ℕ → F
  main_mul : ℕ → F
  op : ℕ → F
  bus_res1 : ℕ → F
  multiplicity : ℕ → F

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- `main_mul` and `main_div` are mutually exclusive: `main_mul * main_div = 0`.
    Named-form mirror of extraction's `constraint_2_every_row`. -/
@[simp]
def main_mul_div_disjoint (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.main_mul row * v.main_div row = 0

/-- `m32` is boolean — named-form mirror of `constraint_40_every_row`. -/
@[simp]
def boolean_m32 (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.m32 row * (1 - v.m32 row) = 0

/-- `na` is boolean — named-form mirror of `constraint_41_every_row`. -/
@[simp]
def boolean_na (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.na row * (1 - v.na row) = 0

/-- `nb` is boolean — named-form mirror of `constraint_42_every_row`. -/
@[simp]
def boolean_nb (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.nb row * (1 - v.nb row) = 0

/-- `nr` is boolean — named-form mirror of `constraint_43_every_row`. -/
@[simp]
def boolean_nr (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.nr row * (1 - v.nr row) = 0

/-- `np` is boolean — named-form mirror of `constraint_44_every_row`. -/
@[simp]
def boolean_np (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.np row * (1 - v.np row) = 0

/-- `sext` is boolean — named-form mirror of `constraint_45_every_row`. -/
@[simp]
def boolean_sext (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.sext row * (1 - v.sext row) = 0

/-- **MUL-subset mode predicates bundled.** The boolean-selector subset
    the compositional MUL proof relies on. -/
@[simp]
def mul_mode_booleans (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  main_mul_div_disjoint v row
  ∧ boolean_m32 v row
  ∧ boolean_na v row
  ∧ boolean_nb v row
  ∧ boolean_nr v row
  ∧ boolean_np v row
  ∧ boolean_sext v row

section BusEmission

open ZiskFv.Airs.OperationBus

/-- Arith's operation-bus emission for a given row, specialized to the MUL
    path (`main_mul = 1`, `main_div = 0`, `div = 0`, `sext = 0`).

    Mirrors the `proves_operation(op:, a:, b:, c:, flag:, mul:)` call at
    `zisk/state-machines/arith/pil/arith.pil:269-270`, specialized
    to the MUL selector. Concretely:

    * `multiplicity` = `multiplicity` witness column (col 41). On active
      MUL rows the PIL constrains it to 1 via the permutation argument.
    * `op` = the Arith `op` witness column (col 39); for MUL this is one
      of `OP_MULU`/`OP_MULUH`/`OP_MULSUH`/`OP_MUL`/`OP_MULH`/`OP_MUL_W`.
    * `a_lo`/`a_hi` = `bus_a0`/`bus_a1` where (since `div = 0` for MUL)
      `bus_a0 = a[0] + a[1] * 2^16`, `bus_a1 = a[2] + a[3] * 2^16`.
    * `b_lo`/`b_hi` = `bus_b0`/`bus_b1` = `b[0] + b[1] * 2^16` and
      `b[2] + b[3] * 2^16`.
    * `c_lo` = `bus_res0`; for MUL-primary (`main_mul = 1`, `main_div = 0`)
      this is `c[0] + c[1] * 2^16` — the low 16+16 bits of the result.
    * `c_hi` = `bus_res1` (the range-checked 32-bit output column);
      constraint 46 pins it to `sext * 0xFFFF_FFFF + (1 - m32) * bus_res1_64`.
      For the MUL case (sext = 0, m32 = 0) this collapses to
      `bus_res1_64 = c[2] + c[3] * 2^16` (main_mul path).
    * `flag` = `div_by_zero`; always 0 on MUL rows.
    * `main_step`/`extended_arg`/`extra_args_0` = 0 (no precompile).

    We expose `bus_res1` as a named column so the compositional proof can
    pin it to the packed high 32 bits via constraint 46 + the MUL-mode
    witnesses (`sext = 0`, `m32 = 0`, `main_mul = 1`, `main_div = 0`).
    The `c_lo` lane derivation from `c[0] + c[1] * 2^16` is exposed
    directly (Arith's `bus_res0` is an `expr`, not a witness column,
    so we recompute it from `c_0` / `c_1` here rather than aliasing). -/
@[simp]
def opBus_row_Arith {F ExtF : Type} [Field F] [Field ExtF]
    (v : Valid_ArithMul F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.multiplicity row
    op := v.op row
    a_lo := v.a_0 row + v.a_1 row * 65536
    a_hi := v.a_2 row + v.a_3 row * 65536
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
    c_lo := v.c_0 row + v.c_1 row * 65536
    c_hi := v.bus_res1 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Arith's operation-bus emission for a MUL-family row in **secondary**
    mode (MULH / MULHU / MULHSU). On these rows `main_mul = 0`,
    `main_div = 0`, so `secondary = 1 - main_mul - main_div = 1` and the
    bus `c` lane comes from `d[]` — the high 64 bits of the product.

    Same row-level layout as `opBus_row_Arith` except the result lane
    `c_lo` is packed from `d[0..1]` rather than `c[0..1]`. The hi-half
    `c_hi := v.bus_res1` is identical; under secondary-mode witnesses
    (`main_mul = 0, main_div = 0, sext = 0, m32 = 0`) constraint 46
    pins it to `d[2] + d[3] * 65536`.

    Mirrors the structure of `opBus_row_ArithDivSecondary`
    (`Airs/Arith/Div.lean:344`). -/
@[simp]
def opBus_row_ArithMulSecondary {F ExtF : Type} [Field F] [Field ExtF]
    (v : Valid_ArithMul F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.multiplicity row
    op := v.op row
    a_lo := v.a_0 row + v.a_1 row * 65536
    a_hi := v.a_2 row + v.a_3 row * 65536
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
    -- High-half result lane: `d[0] + d[1] * 2^16` on secondary = 1.
    c_lo := v.d_0 row + v.d_1 row * 65536
    c_hi := v.bus_res1 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

end BusEmission

/-!
## Carry-chain specialization (MUL-unsigned)

Connects the named-form constraints 31-38 to the pure-field carry-chain
identity in `Airs/Arith/CarryChain.lean`, yielding the packed 128-bit
product identity

    a_packed * b_packed = c_packed + d_packed * 2^64

for the MUL-unsigned mode (`fab = 1`,
`na = nb = np = nr = sext = m32 = div = 0`).

Unsigned mode covers MUL/MULHU/MULW (which use `m32 = 1` but
`na = nb = 0` for the truncation case). Signed-MUL modes (`na` or
`nb` = 1) require a case-split on `(na, nb) ∈ {0,1}²` that sign-adjusts
the operands through the `np`/`nr` selectors via `arith_mul_signed_packed_correct`.
-/

section CarryChain

open ZiskFv.Airs.ArithCarryChain

/-! ## Named-form carry-chain constraints

The named-form predicates below mirror `Arith.extraction.constraint_N_every_row`
for N ∈ {6, 7, 8, 31..38, 46} expressed entirely over the `Valid_ArithMul`
named accessors. They are syntactic literal copies of the extracted
constraint definitions with `Circuit.main circuit (column := N)` rewritten
to the corresponding named field. Used by `arith_mul_*_packed_correct`
and `Bridge/Arith.lean` chain-witness lemmas.

Mappings (per `build/extraction/Extraction/Arith.lean`):
  * col 0..6  → cy_0..cy_6 (carry witnesses)
  * col 7..10 → a_0..a_3 (operand A chunks)
  * col 11..14 → b_0..b_3 (operand B chunks)
  * col 15..18 → c_0..c_3 (low-half result chunks)
  * col 19..22 → d_0..d_3 (high-half result chunks)
  * col 23..29 → na, nb, nr, np, sext, m32, div
  * col 30..32 → fab, na_fb, nb_fa (sign products — F3 additions)
  * col 33..34 → main_div, main_mul
  * col 39 → op, col 40 → bus_res1
-/

/-- Named-form mirror of `constraint_6_every_row`. PIL `arith.pil:58`. -/
@[simp]
def mul_constraint_6_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row - (((1 - 2 * v.na row) - 2 * v.nb row)
    + 4 * v.na row * v.nb row) = 0

/-- Named-form mirror of `constraint_7_every_row`. PIL `arith.pil:59`. -/
@[simp]
def mul_constraint_7_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.na_fb row - v.na row * (1 - 2 * v.nb row) = 0

/-- Named-form mirror of `constraint_8_every_row`. PIL `arith.pil:60`. -/
@[simp]
def mul_constraint_8_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.nb_fa row - v.nb row * (1 - 2 * v.na row) = 0

/-- Named-form mirror of `constraint_31_every_row`. PIL `arith.pil:205`. -/
@[simp]
def mul_constraint_31_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_0 row * v.b_0 row
    - v.c_0 row
    + 2 * v.np row * v.c_0 row
    + v.div row * v.d_0 row
    - 2 * v.nr row * v.d_0 row
    - v.cy_0 row * 65536 = 0

/-- Named-form mirror of `constraint_32_every_row`. PIL `arith.pil:207`. -/
@[simp]
def mul_constraint_32_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_1 row * v.b_0 row + v.fab row * v.a_0 row * v.b_1 row
    - v.c_1 row
    + 2 * v.np row * v.c_1 row
    + v.div row * v.d_1 row
    - 2 * v.nr row * v.d_1 row
    + v.cy_0 row
    - v.cy_1 row * 65536 = 0

/-- Named-form mirror of `constraint_33_every_row`. PIL `arith.pil:209`. -/
@[simp]
def mul_constraint_33_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_2 row * v.b_0 row + v.fab row * v.a_1 row * v.b_1 row
    + v.fab row * v.a_0 row * v.b_2 row
    + v.a_0 row * v.nb_fa row * v.m32 row
    + v.b_0 row * v.na_fb row * v.m32 row
    - v.c_2 row
    + 2 * v.np row * v.c_2 row
    + v.div row * v.d_2 row
    - 2 * v.nr row * v.d_2 row
    - v.np row * v.div row * v.m32 row
    + v.nr row * v.m32 row
    + v.cy_1 row
    - v.cy_2 row * 65536 = 0

/-- Named-form mirror of `constraint_34_every_row`. PIL `arith.pil:211`. -/
@[simp]
def mul_constraint_34_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_0 row + v.fab row * v.a_2 row * v.b_1 row
    + v.fab row * v.a_1 row * v.b_2 row + v.fab row * v.a_0 row * v.b_3 row
    + v.a_1 row * v.nb_fa row * v.m32 row
    + v.b_1 row * v.na_fb row * v.m32 row
    - v.c_3 row
    + 2 * v.np row * v.c_3 row
    + v.div row * v.d_3 row
    - 2 * v.nr row * v.d_3 row
    + v.cy_2 row
    - v.cy_3 row * 65536 = 0

/-- Named-form mirror of `constraint_35_every_row`. PIL `arith.pil:213`. -/
@[simp]
def mul_constraint_35_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
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
    + v.cy_3 row
    - v.cy_4 row * 65536 = 0

/-- Named-form mirror of `constraint_36_every_row`. PIL `arith.pil:215`. -/
@[simp]
def mul_constraint_36_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_2 row + v.fab row * v.a_2 row * v.b_3 row
    + v.b_1 row * v.na_fb row * (1 - v.m32 row)
    + v.a_1 row * v.nb_fa row * (1 - v.m32 row)
    - v.d_1 row * (1 - v.div row)
    + v.d_1 row * 2 * v.np row * (1 - v.div row)
    + v.cy_4 row
    - v.cy_5 row * 65536 = 0

/-- Named-form mirror of `constraint_37_every_row`. PIL `arith.pil:217`. -/
@[simp]
def mul_constraint_37_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.fab row * v.a_3 row * v.b_3 row
    + v.a_2 row * v.nb_fa row * (1 - v.m32 row)
    + v.b_2 row * v.na_fb row * (1 - v.m32 row)
    - v.d_2 row * (1 - v.div row)
    + 2 * v.np row * v.d_2 row * (1 - v.div row)
    + v.cy_5 row
    - v.cy_6 row * 65536 = 0

/-- Named-form mirror of `constraint_38_every_row`. PIL `arith.pil:219`. -/
@[simp]
def mul_constraint_38_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  65536 * v.na row * v.nb row * (1 - v.m32 row)
    + v.a_3 row * v.nb_fa row * (1 - v.m32 row)
    + v.b_3 row * v.na_fb row * (1 - v.m32 row)
    - 65536 * v.np row * (1 - v.div row) * (1 - v.m32 row)
    - v.d_3 row * (1 - v.div row)
    + 2 * v.np row * v.d_3 row * (1 - v.div row)
    + v.cy_6 row = 0

/-- Named-form mirror of `constraint_46_every_row`. PIL `arith.pil:263`.
    Pins `bus_res1` to its mode-specialized value. -/
@[simp]
def mul_constraint_46_named (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  v.bus_res1 row
    - (v.sext row * 4294967295
      + (1 - v.m32 row) * (
          (1 - v.main_mul row - v.main_div row) * (v.d_2 row + v.d_3 row * 65536)
          + v.main_mul row * (v.c_2 row + v.c_3 row * 65536)
          + v.main_div row * (v.a_2 row + v.a_3 row * 65536))) = 0

/-- **Bundled Arith MUL-mode carry-chain constraints.** Packs the 11
    named-form constraints the `arith_mul_unsigned_packed_correct`
    theorem consumes: constraints 6-8 (fab / na_fb / nb_fa closures) plus
    constraints 31-38 (the 8-chunk carry chain). -/
@[simp]
def mul_carry_chain_holds (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  mul_constraint_6_named v row
  ∧ mul_constraint_7_named v row
  ∧ mul_constraint_8_named v row
  ∧ mul_constraint_31_named v row
  ∧ mul_constraint_32_named v row
  ∧ mul_constraint_33_named v row
  ∧ mul_constraint_34_named v row
  ∧ mul_constraint_35_named v row
  ∧ mul_constraint_36_named v row
  ∧ mul_constraint_37_named v row
  ∧ mul_constraint_38_named v row

/-- **Extended Arith MUL-mode row constraints — includes constraint 46.**
    Same shape as `mul_carry_chain_holds` but additionally pins the
    named-form `mul_constraint_46_named` (the `bus_res1` normalization at
    `arith.pil:263`). Required by `equiv_MUL` to discharge the hi-lane
    byte-pack equation via `mul_bus_res1_eq_c_hi`. -/
@[simp]
def mul_row_constraints_with_c46 (v : Valid_ArithMul F ExtF) (row : ℕ) : Prop :=
  mul_carry_chain_holds v row
  ∧ mul_constraint_46_named v row

/-- Project out the carry-chain bundle from the extended bundle. -/
lemma mul_carry_chain_holds_of_extended
    (v : Valid_ArithMul F ExtF) (row : ℕ)
    (h : mul_row_constraints_with_c46 v row) :
    mul_carry_chain_holds v row := h.1

/-- Project out constraint 46 from the extended bundle. -/
lemma mul_constraint_46_of_extended
    (v : Valid_ArithMul F ExtF) (row : ℕ)
    (h : mul_row_constraints_with_c46 v row) :
    mul_constraint_46_named v row := h.2

/-- Packed low-64 value `c_packed := c[0] + c[1] * 2^16 + c[2] * 2^32 + c[3] * 2^48`
    expressed over the named `Valid_ArithMul` columns. For MUL this is the
    low 64 bits of the product. -/
@[simp]
def c_chunks_packed (v : Valid_ArithMul F ExtF) (r : ℕ) : F :=
  v.c_0 r + v.c_1 r * 65536 + v.c_2 r * (65536 * 65536)
    + v.c_3 r * (65536 * 65536 * 65536)

/-- Packed high-64 value `d_packed := d[0] + d[1] * 2^16 + d[2] * 2^32 + d[3] * 2^48`
    over the named `Valid_ArithMul` columns. For MUL this is the high 64 bits. -/
@[simp]
def d_chunks_packed (v : Valid_ArithMul F ExtF) (r : ℕ) : F :=
  v.d_0 r + v.d_1 r * 65536 + v.d_2 r * (65536 * 65536)
    + v.d_3 r * (65536 * 65536 * 65536)

/-- Packed a: `a[0] + a[1] * 2^16 + a[2] * 2^32 + a[3] * 2^48`. -/
@[simp]
def a_chunks_packed (v : Valid_ArithMul F ExtF) (r : ℕ) : F :=
  v.a_0 r + v.a_1 r * 65536 + v.a_2 r * (65536 * 65536)
    + v.a_3 r * (65536 * 65536 * 65536)

/-- Packed b: `b[0] + b[1] * 2^16 + b[2] * 2^32 + b[3] * 2^48`. -/
@[simp]
def b_chunks_packed (v : Valid_ArithMul F ExtF) (r : ℕ) : F :=
  v.b_0 r + v.b_1 r * 65536 + v.b_2 r * (65536 * 65536)
    + v.b_3 r * (65536 * 65536 * 65536)

/-- **MUL-unsigned carry-chain specialization.**

    If the 8 raw extraction carry constraints hold at `v.circuit`
    (constraints 31-38), together with the sign-consistency constraints
    6/7/8 (pinning `fab = 1 - 2na - 2nb + 4na*nb`, `na_fb = na(1-2nb)`,
    `nb_fa = nb(1-2na)`), and the mode witnesses pin
    `na = nb = np = nr = sext = m32 = div = 0`, then the packed chunks
    satisfy

        a_packed * b_packed = c_packed + d_packed * 2^64.

    Direct consequence of `CarryChain.arith_mul_unsigned_carry_identity`:
    after the mode witnesses zero out every selector, constraints 6-8
    pin `fab = 1, na_fb = 0, nb_fa = 0`, and the carry equations reduce
    to exactly the 8-chunk pure-field form the carry-chain lemma closes. -/
lemma arith_mul_unsigned_packed_correct
    (v : Valid_ArithMul F ExtF) (row : ℕ)
    (h6 : mul_constraint_6_named v row)
    (h7 : mul_constraint_7_named v row)
    (h8 : mul_constraint_8_named v row)
    (h31 : mul_constraint_31_named v row)
    (h32 : mul_constraint_32_named v row)
    (h33 : mul_constraint_33_named v row)
    (h34 : mul_constraint_34_named v row)
    (h35 : mul_constraint_35_named v row)
    (h36 : mul_constraint_36_named v row)
    (h37 : mul_constraint_37_named v row)
    (h38 : mul_constraint_38_named v row)
    (h_na : v.na row = 0) (h_nb : v.nb row = 0)
    (h_np : v.np row = 0) (h_nr : v.nr row = 0)
    (_h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 0) :
    a_chunks_packed v row * b_chunks_packed v row
      = c_chunks_packed v row
        + d_chunks_packed v row * (65536 * 65536 * 65536 * 65536) := by
  -- Substitute mode witnesses in named-form constraints; constraints 6/7/8
  -- pin `fab = 1, na_fb = 0, nb_fa = 0`.
  simp only [mul_constraint_6_named, mul_constraint_7_named,
             mul_constraint_8_named, h_na, h_nb,
             mul_zero, add_zero, sub_zero,
             mul_one] at h6 h7 h8
  have h_fab : v.fab row = (1 : F) := by linear_combination h6
  have h_nafb : v.na_fb row = (0 : F) := by linear_combination h7
  have h_nbfa : v.nb_fa row = (0 : F) := by linear_combination h8
  -- Substitute mode + fab/na_fb/nb_fa identities into the carry constraints.
  simp only [mul_constraint_31_named, mul_constraint_32_named,
             mul_constraint_33_named, mul_constraint_34_named,
             mul_constraint_35_named, mul_constraint_36_named,
             mul_constraint_37_named, mul_constraint_38_named,
             h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
             mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- Close via linear combination over the 8 simplified carry equations.
  unfold a_chunks_packed b_chunks_packed c_chunks_packed d_chunks_packed
  linear_combination
    h31
    + 65536 * h32
    + (65536 * 65536) * h33
    + (65536 * 65536 * 65536) * h34
    + (65536 * 65536 * 65536 * 65536) * h35
    + (65536 * 65536 * 65536 * 65536 * 65536) * h36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h38

/-- **MUL-signed carry-chain specialization.**

    Extends `arith_mul_unsigned_packed_correct` to the signed MUL family
    (`(na, nb) ∈ {0,1}²` with `np` matching the product sign). The `nr`,
    `sext`, `m32`, `div` witnesses remain zero — signed-MUL 64-bit uses
    the same 64×64→128 carry chain as unsigned; only the sign-preprocess
    witnesses differ.

    The conclusion mirrors the pure-field
    `ArithCarryChain.arith_mul_signed_carry_identity`:

        fab * a_packed * b_packed
          + (nb_fa * a_packed + na_fb * b_packed) * B^4
          + (na*nb - np) * B^8
        = (1 - 2*np) * (c_packed + d_packed * B^4)

    where `fab`, `na_fb`, `nb_fa` are the named columns pinned by
    constraints 6/7/8 to
        fab = 1 - 2*na - 2*nb + 4*na*nb,
        na_fb = na*(1 - 2*nb),
        nb_fa = nb*(1 - 2*na).
    The caller may specialize `(na, nb, np)` to any of the four MUL-mode
    quadrants to recover a concrete sign-adjusted packed identity; the
    unsigned specialization (`na = nb = np = 0`) reduces the LHS to
    `a_packed * b_packed` and the RHS to `c_packed + d_packed * B^4`.

    The arith_table permutation lookup enforces the 9-opcode mapping
    `(opcode, m32) ↦ (na, nb, np, nr)`. This theorem takes the sign
    witnesses as explicit hypotheses; callers derive them from the
    table via `Airs/Arith/ArithTable.lean`. -/
lemma arith_mul_signed_packed_correct
    (v : Valid_ArithMul F ExtF) (row : ℕ)
    (h6 : mul_constraint_6_named v row)
    (h7 : mul_constraint_7_named v row)
    (h8 : mul_constraint_8_named v row)
    (h31 : mul_constraint_31_named v row)
    (h32 : mul_constraint_32_named v row)
    (h33 : mul_constraint_33_named v row)
    (h34 : mul_constraint_34_named v row)
    (h35 : mul_constraint_35_named v row)
    (h36 : mul_constraint_36_named v row)
    (h37 : mul_constraint_37_named v row)
    (h38 : mul_constraint_38_named v row)
    (h_nr : v.nr row = 0)
    (_h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 0) :
    (1 - 2 * v.na row - 2 * v.nb row + 4 * v.na row * v.nb row)
        * a_chunks_packed v row * b_chunks_packed v row
      + (v.nb row * (1 - 2 * v.na row) * a_chunks_packed v row
          + v.na row * (1 - 2 * v.nb row) * b_chunks_packed v row)
          * (65536 * 65536 * 65536 * 65536)
      + (v.na row * v.nb row - v.np row)
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np row)
          * (c_chunks_packed v row
            + d_chunks_packed v row * (65536 * 65536 * 65536 * 65536)) := by
  -- Derive fab / na_fb / nb_fa equalities from named-form constraints 6/7/8.
  have h_fab : v.fab row = 1 - 2 * v.na row - 2 * v.nb row
      + 4 * v.na row * v.nb row := by
    simp only [mul_constraint_6_named] at h6
    linear_combination h6
  have h_nafb : v.na_fb row = v.na row * (1 - 2 * v.nb row) := by
    simp only [mul_constraint_7_named] at h7
    linear_combination h7
  have h_nbfa : v.nb_fa row = v.nb row * (1 - 2 * v.na row) := by
    simp only [mul_constraint_8_named] at h8
    linear_combination h8
  -- Substitute mode witnesses (m32 = 0, nr = 0, div = 0) and the fab / na_fb / nb_fa
  -- identities.
  simp only [mul_constraint_31_named, mul_constraint_32_named,
             mul_constraint_33_named, mul_constraint_34_named,
             mul_constraint_35_named, mul_constraint_36_named,
             mul_constraint_37_named, mul_constraint_38_named,
             h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero,
             mul_one]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- The signed carry-chain identity now applies.
  unfold a_chunks_packed b_chunks_packed c_chunks_packed d_chunks_packed
  linear_combination
    h31
    + 65536 * h32
    + (65536 * 65536) * h33
    + (65536 * 65536 * 65536) * h34
    + (65536 * 65536 * 65536 * 65536) * h35
    + (65536 * 65536 * 65536 * 65536 * 65536) * h36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h38

/-- **MUL-unsigned carry-chain specialization (bundled form).** Same as
    `arith_mul_unsigned_packed_correct` but consuming the bundled
    `mul_carry_chain_holds` predicate — more ergonomic for downstream
    consumers. -/
lemma arith_mul_unsigned_packed_correct_bundled
    (v : Valid_ArithMul F ExtF) (row : ℕ)
    (h_chain : mul_carry_chain_holds v row)
    (h_na : v.na row = 0) (h_nb : v.nb row = 0)
    (h_np : v.np row = 0) (h_nr : v.nr row = 0)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 0) :
    a_chunks_packed v row * b_chunks_packed v row
      = c_chunks_packed v row
        + d_chunks_packed v row * (65536 * 65536 * 65536 * 65536) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact arith_mul_unsigned_packed_correct v row h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_na h_nb h_np h_nr h_sext h_m32 h_div

/-- **MUL-signed carry-chain specialization (bundled form).** Same as
    `arith_mul_signed_packed_correct` but consuming the bundled
    `mul_carry_chain_holds` predicate. Used by the bridge
    `mul_signed_chain_witnesses` to extract per-chunk identities over
    named columns for downstream consumption by the signed ℤ
    aggregator. -/
lemma arith_mul_signed_packed_correct_bundled
    (v : Valid_ArithMul F ExtF) (row : ℕ)
    (h_chain : mul_carry_chain_holds v row)
    (h_nr : v.nr row = 0)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 0) :
    (1 - 2 * v.na row - 2 * v.nb row + 4 * v.na row * v.nb row)
        * a_chunks_packed v row * b_chunks_packed v row
      + (v.nb row * (1 - 2 * v.na row) * a_chunks_packed v row
          + v.na row * (1 - 2 * v.nb row) * b_chunks_packed v row)
          * (65536 * 65536 * 65536 * 65536)
      + (v.na row * v.nb row - v.np row)
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np row)
          * (c_chunks_packed v row
            + d_chunks_packed v row * (65536 * 65536 * 65536 * 65536)) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact arith_mul_signed_packed_correct v row h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_nr h_sext h_m32 h_div

end CarryChain

end ZiskFv.Airs.ArithMul
