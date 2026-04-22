import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Arith
import ZiskFv.Airs.OperationBus

/-!
Named-column mirror of the ZisK `Arith` AIR, restricted to the MUL subset.

The Arith state machine is the heavy-weight multiplier behind RV64 MUL/MULH
family. Its PIL lives at `vendor/zisk/state-machines/arith/pil/arith.pil`. Unlike
`BinaryAdd` (which is a narrow carry-chain AIR with 9 constraints, 4 core),
Arith carries 65 constraints spanning the 8-chunk carry chains for a full 64×64
multiply-divide, sign-extension witnesses, and the arith_table / arith_range_table
lookups.

Phase 2 archetype A5 **does not derive** Arith's correctness from the carry
chains — that proof would require lifting the 8-chunk byte-level decomposition
to `BitVec 128` arithmetic (roughly what openvm-fv's `Spec/Mul.lean` does for
4-byte MUL over BabyBear, scaled up 4× and over Goldilocks). Instead we follow
the BEQ pattern: model the AIR's bus-emission projection as a named
`OperationBusEntry`, and parameterize the compositional theorem on "Arith's
`c` lanes encode `a * b`". That hypothesis is delegated to Phase 4 audit.

Mirrors `Airs/Binary/BinaryAdd.lean` in structure — named columns for the
cells the bus-emission uses, plus `constraint_N_of_extraction` bridges for the
MUL-subset constraints (`main_mul * main_div = 0`, the binary selectors, and
the carry-chain equations that a Phase 4 auditor will unfold).
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

/-- **MUL-subset mode predicates bundled.** The boolean-selector subset the
    compositional MUL proof relies on. The carry-chain constraints (31–38)
    remain reachable via the raw extraction bridges below; they are carried
    through to the Phase-4 audit but not consumed by the Phase-2 archetype
    proof (which parameterizes over the resulting `c = a * b` property). -/
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
    `vendor/zisk/state-machines/arith/pil/arith.pil:269-270`, specialized
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

end ZiskFv.Airs.ArithMul
