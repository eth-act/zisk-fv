import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import Extraction.Arith
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.Arith.CarryChain

/-!
Named-column mirror of the ZisK `Arith` AIR, restricted to the MUL subset.

The Arith state machine is the multiplier behind the RV64 MUL/MULH family
(PIL: `zisk/state-machines/arith/pil/arith.pil`). It carries 65
constraints spanning 8-chunk carry chains for full 64×64 multiply-divide,
sign-extension witnesses, and the arith_table / arith_range_table lookups.

This file exposes named columns for the cells the bus-emission uses, plus
`constraint_N_of_extraction` bridges for the MUL-subset constraints
(`main_mul * main_div = 0`, the binary selectors, and the carry-chain
equations).
-/

namespace ZiskFv.Airs.ArithMul

open Goldilocks
open Arith.extraction

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
structure Valid_ArithMul (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
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
  main_div : ℕ → F
  main_mul : ℕ → F
  op : ℕ → F
  bus_res1 : ℕ → F
  multiplicity : ℕ → F
  a_0_def : ∀ row,
    a_0 row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  a_1_def : ∀ row,
    a_1 row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  a_2_def : ∀ row,
    a_2 row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  a_3_def : ∀ row,
    a_3 row = Circuit.main circuit (id := 1) (column := 10) (row := row) (rotation := 0)
  b_0_def : ∀ row,
    b_0 row = Circuit.main circuit (id := 1) (column := 11) (row := row) (rotation := 0)
  b_1_def : ∀ row,
    b_1 row = Circuit.main circuit (id := 1) (column := 12) (row := row) (rotation := 0)
  b_2_def : ∀ row,
    b_2 row = Circuit.main circuit (id := 1) (column := 13) (row := row) (rotation := 0)
  b_3_def : ∀ row,
    b_3 row = Circuit.main circuit (id := 1) (column := 14) (row := row) (rotation := 0)
  c_0_def : ∀ row,
    c_0 row = Circuit.main circuit (id := 1) (column := 15) (row := row) (rotation := 0)
  c_1_def : ∀ row,
    c_1 row = Circuit.main circuit (id := 1) (column := 16) (row := row) (rotation := 0)
  c_2_def : ∀ row,
    c_2 row = Circuit.main circuit (id := 1) (column := 17) (row := row) (rotation := 0)
  c_3_def : ∀ row,
    c_3 row = Circuit.main circuit (id := 1) (column := 18) (row := row) (rotation := 0)
  d_0_def : ∀ row,
    d_0 row = Circuit.main circuit (id := 1) (column := 19) (row := row) (rotation := 0)
  d_1_def : ∀ row,
    d_1 row = Circuit.main circuit (id := 1) (column := 20) (row := row) (rotation := 0)
  d_2_def : ∀ row,
    d_2 row = Circuit.main circuit (id := 1) (column := 21) (row := row) (rotation := 0)
  d_3_def : ∀ row,
    d_3 row = Circuit.main circuit (id := 1) (column := 22) (row := row) (rotation := 0)
  na_def : ∀ row,
    na row = Circuit.main circuit (id := 1) (column := 23) (row := row) (rotation := 0)
  nb_def : ∀ row,
    nb row = Circuit.main circuit (id := 1) (column := 24) (row := row) (rotation := 0)
  nr_def : ∀ row,
    nr row = Circuit.main circuit (id := 1) (column := 25) (row := row) (rotation := 0)
  np_def : ∀ row,
    np row = Circuit.main circuit (id := 1) (column := 26) (row := row) (rotation := 0)
  sext_def : ∀ row,
    sext row = Circuit.main circuit (id := 1) (column := 27) (row := row) (rotation := 0)
  m32_def : ∀ row,
    m32 row = Circuit.main circuit (id := 1) (column := 28) (row := row) (rotation := 0)
  div_def : ∀ row,
    div row = Circuit.main circuit (id := 1) (column := 29) (row := row) (rotation := 0)
  main_div_def : ∀ row,
    main_div row = Circuit.main circuit (id := 1) (column := 33) (row := row) (rotation := 0)
  main_mul_def : ∀ row,
    main_mul row = Circuit.main circuit (id := 1) (column := 34) (row := row) (rotation := 0)
  op_def : ∀ row,
    op row = Circuit.main circuit (id := 1) (column := 39) (row := row) (rotation := 0)
  bus_res1_def : ∀ row,
    bus_res1 row = Circuit.main circuit (id := 1) (column := 40) (row := row) (rotation := 0)
  multiplicity_def : ∀ row,
    multiplicity row = Circuit.main circuit (id := 1) (column := 41) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- `main_mul` and `main_div` are mutually exclusive: `main_mul * main_div = 0`.
    Rewrites `constraint_2_every_row`. -/
@[simp]
def main_mul_div_disjoint (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.main_mul row * v.main_div row = 0

/-- `m32` is boolean — rewrites `constraint_40_every_row`. -/
@[simp]
def boolean_m32 (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.m32 row * (1 - v.m32 row) = 0

/-- `na` is boolean — rewrites `constraint_41_every_row`. -/
@[simp]
def boolean_na (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.na row * (1 - v.na row) = 0

/-- `nb` is boolean — rewrites `constraint_42_every_row`. -/
@[simp]
def boolean_nb (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.nb row * (1 - v.nb row) = 0

/-- `nr` is boolean — rewrites `constraint_43_every_row`. -/
@[simp]
def boolean_nr (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.nr row * (1 - v.nr row) = 0

/-- `np` is boolean — rewrites `constraint_44_every_row`. -/
@[simp]
def boolean_np (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.np row * (1 - v.np row) = 0

/-- `sext` is boolean — rewrites `constraint_45_every_row`. -/
@[simp]
def boolean_sext (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  v.sext row * (1 - v.sext row) = 0

/-- **MUL-subset mode predicates bundled.** The boolean-selector subset
    the compositional MUL proof relies on. The carry-chain constraints
    (31–38) remain reachable via the raw extraction bridges below. -/
@[simp]
def mul_mode_booleans (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  main_mul_div_disjoint v row
  ∧ boolean_m32 v row
  ∧ boolean_na v row
  ∧ boolean_nb v row
  ∧ boolean_nr v row
  ∧ boolean_np v row
  ∧ boolean_sext v row

section extraction_bridge

@[simp]
lemma constraint_2_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_2_every_row v.circuit row ↔ main_mul_div_disjoint v row := by
  unfold constraint_2_every_row main_mul_div_disjoint
  rw [v.main_mul_def, v.main_div_def]

@[simp]
lemma constraint_40_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_40_every_row v.circuit row ↔ boolean_m32 v row := by
  unfold constraint_40_every_row boolean_m32
  rw [v.m32_def]

@[simp]
lemma constraint_41_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_41_every_row v.circuit row ↔ boolean_na v row := by
  unfold constraint_41_every_row boolean_na
  rw [v.na_def]

@[simp]
lemma constraint_42_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_42_every_row v.circuit row ↔ boolean_nb v row := by
  unfold constraint_42_every_row boolean_nb
  rw [v.nb_def]

@[simp]
lemma constraint_43_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_43_every_row v.circuit row ↔ boolean_nr v row := by
  unfold constraint_43_every_row boolean_nr
  rw [v.nr_def]

@[simp]
lemma constraint_44_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_44_every_row v.circuit row ↔ boolean_np v row := by
  unfold constraint_44_every_row boolean_np
  rw [v.np_def]

@[simp]
lemma constraint_45_of_extraction
    (v : Valid_ArithMul C F ExtF) (row : ℕ) :
    constraint_45_every_row v.circuit row ↔ boolean_sext v row := by
  unfold constraint_45_every_row boolean_sext
  rw [v.sext_def]

end extraction_bridge

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
def opBus_row_Arith {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (v : Valid_ArithMul C F ExtF) (row : ℕ) : OperationBusEntry F :=
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

end BusEmission

/-!
## Carry-chain specialization (MUL-unsigned)

Connects the raw extraction constraints 31-38 at `v.circuit` to the
pure-field carry-chain identity in `Airs/Arith/CarryChain.lean`,
yielding the packed 128-bit product identity

    a_packed * b_packed = c_packed + d_packed * 2^64

for the MUL-unsigned mode (`fab = 1`,
`na = nb = np = nr = sext = m32 = div = 0`).

The theorem extracts the seven carry witnesses directly from the
circuit projection at columns 0-6, unfolds the raw constraints, and
applies `ZiskFv.Airs.ArithCarryChain.arith_mul_unsigned_carry_identity`.

Unsigned mode covers MUL/MULHU/MULW (which use `m32 = 1` but
`na = nb = 0` for the truncation case). Signed-MUL modes (`na` or
`nb` = 1) require a case-split on `(na, nb) ∈ {0,1}²` that sign-adjusts
the operands through the `np`/`nr` selectors and are out of scope here.
-/

section CarryChain

open Arith.extraction
open ZiskFv.Airs.ArithCarryChain

/-- **Bundled Arith MUL-mode carry-chain constraints.** Packs the 11
    extraction constraints the `arith_mul_unsigned_packed_correct`
    theorem consumes: constraints 6-8 (fab / na_fb / nb_fa closures) plus
    constraints 31-38 (the 8-chunk carry chain). -/
@[simp]
def mul_carry_chain_holds (v : Valid_ArithMul C F ExtF) (row : ℕ) : Prop :=
  constraint_6_every_row v.circuit row
  ∧ constraint_7_every_row v.circuit row
  ∧ constraint_8_every_row v.circuit row
  ∧ constraint_31_every_row v.circuit row
  ∧ constraint_32_every_row v.circuit row
  ∧ constraint_33_every_row v.circuit row
  ∧ constraint_34_every_row v.circuit row
  ∧ constraint_35_every_row v.circuit row
  ∧ constraint_36_every_row v.circuit row
  ∧ constraint_37_every_row v.circuit row
  ∧ constraint_38_every_row v.circuit row

/-- Packed low-64 value `c_packed := c[0] + c[1] * 2^16 + c[2] * 2^32 + c[3] * 2^48`
    expressed over the named `Valid_ArithMul` columns. For MUL this is the
    low 64 bits of the product. -/
@[simp]
def c_chunks_packed (v : Valid_ArithMul C F ExtF) (r : ℕ) : F :=
  v.c_0 r + v.c_1 r * 65536 + v.c_2 r * (65536 * 65536)
    + v.c_3 r * (65536 * 65536 * 65536)

/-- Packed high-64 value `d_packed := d[0] + d[1] * 2^16 + d[2] * 2^32 + d[3] * 2^48`
    over the named `Valid_ArithMul` columns. For MUL this is the high 64 bits. -/
@[simp]
def d_chunks_packed (v : Valid_ArithMul C F ExtF) (r : ℕ) : F :=
  v.d_0 r + v.d_1 r * 65536 + v.d_2 r * (65536 * 65536)
    + v.d_3 r * (65536 * 65536 * 65536)

/-- Packed a: `a[0] + a[1] * 2^16 + a[2] * 2^32 + a[3] * 2^48`. -/
@[simp]
def a_chunks_packed (v : Valid_ArithMul C F ExtF) (r : ℕ) : F :=
  v.a_0 r + v.a_1 r * 65536 + v.a_2 r * (65536 * 65536)
    + v.a_3 r * (65536 * 65536 * 65536)

/-- Packed b: `b[0] + b[1] * 2^16 + b[2] * 2^32 + b[3] * 2^48`. -/
@[simp]
def b_chunks_packed (v : Valid_ArithMul C F ExtF) (r : ℕ) : F :=
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
    (v : Valid_ArithMul C F ExtF) (row : ℕ)
    (h6 : constraint_6_every_row v.circuit row)
    (h7 : constraint_7_every_row v.circuit row)
    (h8 : constraint_8_every_row v.circuit row)
    (h31 : constraint_31_every_row v.circuit row)
    (h32 : constraint_32_every_row v.circuit row)
    (h33 : constraint_33_every_row v.circuit row)
    (h34 : constraint_34_every_row v.circuit row)
    (h35 : constraint_35_every_row v.circuit row)
    (h36 : constraint_36_every_row v.circuit row)
    (h37 : constraint_37_every_row v.circuit row)
    (h38 : constraint_38_every_row v.circuit row)
    (h_na : v.na row = 0) (h_nb : v.nb row = 0)
    (h_np : v.np row = 0) (h_nr : v.nr row = 0)
    (_h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_div : v.div row = 0) :
    a_chunks_packed v row * b_chunks_packed v row
      = c_chunks_packed v row
        + d_chunks_packed v row * (65536 * 65536 * 65536 * 65536) := by
  -- Rewrite the constraints to named-column form and substitute the mode.
  -- Unfold named columns via their *_def equations, which rewrite back to
  -- Circuit.main. After ring_nf, each selector column becomes a free symbol;
  -- with the 7 mode zeros, the `fab` / `na_fb` / `nb_fa` columns are the
  -- only remaining mode atoms. Constraints 6/7/8 give us
  --   fab = 1,  na_fb = 0,  nb_fa = 0
  -- after substituting na = nb = 0 via h_na / h_nb.
  simp only [constraint_6_every_row, constraint_7_every_row, constraint_8_every_row,
             ← v.na_def, ← v.nb_def] at h6 h7 h8
  simp only [h_na, h_nb] at h6 h7 h8
  -- Extract the `fab = 1`, `na_fb = 0`, `nb_fa = 0` equalities in linear form.
  have h_fab : Circuit.main v.circuit (id := 1) (column := 30) (row := row) (rotation := 0)
    = (1 : F) := by linear_combination h6
  have h_nafb : Circuit.main v.circuit (id := 1) (column := 31) (row := row) (rotation := 0)
    = (0 : F) := by linear_combination h7
  have h_nbfa : Circuit.main v.circuit (id := 1) (column := 32) (row := row) (rotation := 0)
    = (0 : F) := by linear_combination h8
  -- Unfold the carry constraints and rewrite named columns back.
  simp only [constraint_31_every_row, constraint_32_every_row,
             constraint_33_every_row, constraint_34_every_row,
             constraint_35_every_row, constraint_36_every_row,
             constraint_37_every_row, constraint_38_every_row,
             ← v.a_0_def, ← v.a_1_def, ← v.a_2_def, ← v.a_3_def,
             ← v.b_0_def, ← v.b_1_def, ← v.b_2_def, ← v.b_3_def,
             ← v.c_0_def, ← v.c_1_def, ← v.c_2_def, ← v.c_3_def,
             ← v.d_0_def, ← v.d_1_def, ← v.d_2_def, ← v.d_3_def,
             ← v.na_def, ← v.nb_def, ← v.np_def, ← v.nr_def,
             ← v.m32_def, ← v.div_def]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- Use simp to apply the (possibly-missing) mode witnesses.
  simp only [h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
             mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- The carry-chain identity now applies at (a_i, b_i, c_i, d_i, carry_i).
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
    (v : Valid_ArithMul C F ExtF) (row : ℕ)
    (h6 : constraint_6_every_row v.circuit row)
    (h7 : constraint_7_every_row v.circuit row)
    (h8 : constraint_8_every_row v.circuit row)
    (h31 : constraint_31_every_row v.circuit row)
    (h32 : constraint_32_every_row v.circuit row)
    (h33 : constraint_33_every_row v.circuit row)
    (h34 : constraint_34_every_row v.circuit row)
    (h35 : constraint_35_every_row v.circuit row)
    (h36 : constraint_36_every_row v.circuit row)
    (h37 : constraint_37_every_row v.circuit row)
    (h38 : constraint_38_every_row v.circuit row)
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
  -- Derive fab / na_fb / nb_fa from constraints 6/7/8.
  simp only [constraint_6_every_row, constraint_7_every_row, constraint_8_every_row,
             ← v.na_def, ← v.nb_def] at h6 h7 h8
  have h_fab : Circuit.main v.circuit (id := 1) (column := 30) (row := row) (rotation := 0)
    = 1 - 2 * v.na row - 2 * v.nb row + 4 * v.na row * v.nb row := by linear_combination h6
  have h_nafb : Circuit.main v.circuit (id := 1) (column := 31) (row := row) (rotation := 0)
    = v.na row * (1 - 2 * v.nb row) := by linear_combination h7
  have h_nbfa : Circuit.main v.circuit (id := 1) (column := 32) (row := row) (rotation := 0)
    = v.nb row * (1 - 2 * v.na row) := by linear_combination h8
  -- Unfold the carry constraints and rewrite named columns back.
  simp only [constraint_31_every_row, constraint_32_every_row,
             constraint_33_every_row, constraint_34_every_row,
             constraint_35_every_row, constraint_36_every_row,
             constraint_37_every_row, constraint_38_every_row,
             ← v.a_0_def, ← v.a_1_def, ← v.a_2_def, ← v.a_3_def,
             ← v.b_0_def, ← v.b_1_def, ← v.b_2_def, ← v.b_3_def,
             ← v.c_0_def, ← v.c_1_def, ← v.c_2_def, ← v.c_3_def,
             ← v.d_0_def, ← v.d_1_def, ← v.d_2_def, ← v.d_3_def,
             ← v.na_def, ← v.nb_def, ← v.np_def, ← v.nr_def,
             ← v.m32_def, ← v.div_def]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- Substitute mode witnesses (m32 = 0, nr = 0, div = 0) and the fab / na_fb / nb_fa
  -- identities.
  simp only [h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
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
    (v : Valid_ArithMul C F ExtF) (row : ℕ)
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
    `mul_carry_chain_holds` predicate. Used by the Step 4.alpha.A
    bridge `mul_signed_chain_witnesses` to extract per-chunk identities
    over named columns for downstream consumption by the signed ℤ
    aggregator. -/
lemma arith_mul_signed_packed_correct_bundled
    (v : Valid_ArithMul C F ExtF) (row : ℕ)
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
