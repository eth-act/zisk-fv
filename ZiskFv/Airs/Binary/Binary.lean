import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import Extraction.Binary

/-!
Named-column mirror of the extracted ZisK `Binary` AIR (pilout idx 10),
plus `constraint_N_of_extraction` iff-lemmas bridging each named predicate
back to `Binary.extraction.constraint_N_every_row`.

Mirrors `Airs/Binary/BinaryAdd.lean`. Only the seven F-typed constraints
(0..6) are bridged here; constraints 7–13 are skipped at the extraction
layer because they mix `F` (witness cells) with `ExtF` (challenges) — those
are the lookup-permutation interactions and are handled compositionally
via `Airs/BinaryTable.lean`'s `bin_table_consumer_wf` axiom.
-/

namespace ZiskFv.Airs.Binary

open Goldilocks
open Binary.extraction

/-- Named accessors for one row of ZisK's `Binary` AIR.

    Column layout taken from the witness-column header in
    `ZiskFv/ZiskFv/Extraction/Binary.lean` (stage-1 cols 0–38, stage-2
    cols 0–4). Stage-1 columns:
    * 0: `b_op`
    * 1..8: `free_in_a[0..7]`
    * 9..16: `free_in_b[0..7]`
    * 17..24: `free_in_c[0..7]`
    * 25..32: `carry[0..7]`
    * 33: `mode32`
    * 34: `result_is_a`
    * 35: `use_first_byte`
    * 36: `c_is_signed`
    * 37: `b_op_or_sext`
    * 38: `mode32_and_c_is_signed`
    Stage-2 columns:
    * 0: `gsum`
    * 1..4: `im[0..3]`
-/
structure Valid_Binary (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  /-- Operation literal (one of the `OP_*` constants in `Airs/BinaryTable.lean`). -/
  b_op : ℕ → F
  free_in_a_0 : ℕ → F
  free_in_a_1 : ℕ → F
  free_in_a_2 : ℕ → F
  free_in_a_3 : ℕ → F
  free_in_a_4 : ℕ → F
  free_in_a_5 : ℕ → F
  free_in_a_6 : ℕ → F
  free_in_a_7 : ℕ → F
  free_in_b_0 : ℕ → F
  free_in_b_1 : ℕ → F
  free_in_b_2 : ℕ → F
  free_in_b_3 : ℕ → F
  free_in_b_4 : ℕ → F
  free_in_b_5 : ℕ → F
  free_in_b_6 : ℕ → F
  free_in_b_7 : ℕ → F
  free_in_c_0 : ℕ → F
  free_in_c_1 : ℕ → F
  free_in_c_2 : ℕ → F
  free_in_c_3 : ℕ → F
  free_in_c_4 : ℕ → F
  free_in_c_5 : ℕ → F
  free_in_c_6 : ℕ → F
  free_in_c_7 : ℕ → F
  carry_0 : ℕ → F
  carry_1 : ℕ → F
  carry_2 : ℕ → F
  carry_3 : ℕ → F
  carry_4 : ℕ → F
  carry_5 : ℕ → F
  carry_6 : ℕ → F
  carry_7 : ℕ → F
  /-- 32-bit-mode flag. -/
  mode32 : ℕ → F
  /-- Auxiliary: `result == a` shortcut (true for some compare/min-max paths). -/
  result_is_a : ℕ → F
  /-- Auxiliary: only the first byte of the result is meaningful. -/
  use_first_byte : ℕ → F
  /-- Auxiliary: this row's operation is signed (affects compare/sign-extension). -/
  c_is_signed : ℕ → F
  /-- Linear combination of `b_op`, `mode32`, `c_is_signed` used to drive
      sign-extension lookups in upper bytes. -/
  b_op_or_sext : ℕ → F
  /-- Product `mode32 * c_is_signed`. -/
  mode32_and_c_is_signed : ℕ → F
  /-- Stage-2 permutation accumulator. -/
  gsum : ℕ → F
  im_0 : ℕ → F
  im_1 : ℕ → F
  im_2 : ℕ → F
  im_3 : ℕ → F
  /-- Agreement with the extraction layer: each named field refers back to the
      same cell the raw `Circuit.main` accessor would. -/
  b_op_def : ∀ row,
    b_op row = Circuit.main circuit (id := 1) (column := 0) (row := row) (rotation := 0)
  free_in_a_0_def : ∀ row,
    free_in_a_0 row = Circuit.main circuit (id := 1) (column := 1) (row := row) (rotation := 0)
  free_in_a_1_def : ∀ row,
    free_in_a_1 row = Circuit.main circuit (id := 1) (column := 2) (row := row) (rotation := 0)
  free_in_a_2_def : ∀ row,
    free_in_a_2 row = Circuit.main circuit (id := 1) (column := 3) (row := row) (rotation := 0)
  free_in_a_3_def : ∀ row,
    free_in_a_3 row = Circuit.main circuit (id := 1) (column := 4) (row := row) (rotation := 0)
  free_in_a_4_def : ∀ row,
    free_in_a_4 row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  free_in_a_5_def : ∀ row,
    free_in_a_5 row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  free_in_a_6_def : ∀ row,
    free_in_a_6 row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  free_in_a_7_def : ∀ row,
    free_in_a_7 row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  free_in_b_0_def : ∀ row,
    free_in_b_0 row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  free_in_b_1_def : ∀ row,
    free_in_b_1 row = Circuit.main circuit (id := 1) (column := 10) (row := row) (rotation := 0)
  free_in_b_2_def : ∀ row,
    free_in_b_2 row = Circuit.main circuit (id := 1) (column := 11) (row := row) (rotation := 0)
  free_in_b_3_def : ∀ row,
    free_in_b_3 row = Circuit.main circuit (id := 1) (column := 12) (row := row) (rotation := 0)
  free_in_b_4_def : ∀ row,
    free_in_b_4 row = Circuit.main circuit (id := 1) (column := 13) (row := row) (rotation := 0)
  free_in_b_5_def : ∀ row,
    free_in_b_5 row = Circuit.main circuit (id := 1) (column := 14) (row := row) (rotation := 0)
  free_in_b_6_def : ∀ row,
    free_in_b_6 row = Circuit.main circuit (id := 1) (column := 15) (row := row) (rotation := 0)
  free_in_b_7_def : ∀ row,
    free_in_b_7 row = Circuit.main circuit (id := 1) (column := 16) (row := row) (rotation := 0)
  free_in_c_0_def : ∀ row,
    free_in_c_0 row = Circuit.main circuit (id := 1) (column := 17) (row := row) (rotation := 0)
  free_in_c_1_def : ∀ row,
    free_in_c_1 row = Circuit.main circuit (id := 1) (column := 18) (row := row) (rotation := 0)
  free_in_c_2_def : ∀ row,
    free_in_c_2 row = Circuit.main circuit (id := 1) (column := 19) (row := row) (rotation := 0)
  free_in_c_3_def : ∀ row,
    free_in_c_3 row = Circuit.main circuit (id := 1) (column := 20) (row := row) (rotation := 0)
  free_in_c_4_def : ∀ row,
    free_in_c_4 row = Circuit.main circuit (id := 1) (column := 21) (row := row) (rotation := 0)
  free_in_c_5_def : ∀ row,
    free_in_c_5 row = Circuit.main circuit (id := 1) (column := 22) (row := row) (rotation := 0)
  free_in_c_6_def : ∀ row,
    free_in_c_6 row = Circuit.main circuit (id := 1) (column := 23) (row := row) (rotation := 0)
  free_in_c_7_def : ∀ row,
    free_in_c_7 row = Circuit.main circuit (id := 1) (column := 24) (row := row) (rotation := 0)
  carry_0_def : ∀ row,
    carry_0 row = Circuit.main circuit (id := 1) (column := 25) (row := row) (rotation := 0)
  carry_1_def : ∀ row,
    carry_1 row = Circuit.main circuit (id := 1) (column := 26) (row := row) (rotation := 0)
  carry_2_def : ∀ row,
    carry_2 row = Circuit.main circuit (id := 1) (column := 27) (row := row) (rotation := 0)
  carry_3_def : ∀ row,
    carry_3 row = Circuit.main circuit (id := 1) (column := 28) (row := row) (rotation := 0)
  carry_4_def : ∀ row,
    carry_4 row = Circuit.main circuit (id := 1) (column := 29) (row := row) (rotation := 0)
  carry_5_def : ∀ row,
    carry_5 row = Circuit.main circuit (id := 1) (column := 30) (row := row) (rotation := 0)
  carry_6_def : ∀ row,
    carry_6 row = Circuit.main circuit (id := 1) (column := 31) (row := row) (rotation := 0)
  carry_7_def : ∀ row,
    carry_7 row = Circuit.main circuit (id := 1) (column := 32) (row := row) (rotation := 0)
  mode32_def : ∀ row,
    mode32 row = Circuit.main circuit (id := 1) (column := 33) (row := row) (rotation := 0)
  result_is_a_def : ∀ row,
    result_is_a row = Circuit.main circuit (id := 1) (column := 34) (row := row) (rotation := 0)
  use_first_byte_def : ∀ row,
    use_first_byte row = Circuit.main circuit (id := 1) (column := 35) (row := row) (rotation := 0)
  c_is_signed_def : ∀ row,
    c_is_signed row = Circuit.main circuit (id := 1) (column := 36) (row := row) (rotation := 0)
  b_op_or_sext_def : ∀ row,
    b_op_or_sext row = Circuit.main circuit (id := 1) (column := 37) (row := row) (rotation := 0)
  mode32_and_c_is_signed_def : ∀ row,
    mode32_and_c_is_signed row = Circuit.main circuit (id := 1) (column := 38) (row := row) (rotation := 0)
  gsum_def : ∀ row,
    gsum row = Circuit.main circuit (id := 2) (column := 0) (row := row) (rotation := 0)
  im_0_def : ∀ row,
    im_0 row = Circuit.main circuit (id := 2) (column := 1) (row := row) (rotation := 0)
  im_1_def : ∀ row,
    im_1 row = Circuit.main circuit (id := 2) (column := 2) (row := row) (rotation := 0)
  im_2_def : ∀ row,
    im_2 row = Circuit.main circuit (id := 2) (column := 3) (row := row) (rotation := 0)
  im_3_def : ∀ row,
    im_3 row = Circuit.main circuit (id := 2) (column := 4) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- `mode32` is boolean — rewrites `constraint_0_every_row`. -/
@[simp]
def boolean_mode32 (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.mode32 row * (1 - v.mode32 row) = 0

/-- `carry[7]` is boolean — rewrites `constraint_1_every_row`. -/
@[simp]
def boolean_carry_7 (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.carry_7 row * (1 - v.carry_7 row) = 0

/-- `result_is_a` is boolean — rewrites `constraint_2_every_row`. -/
@[simp]
def boolean_result_is_a (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.result_is_a row * (1 - v.result_is_a row) = 0

/-- `use_first_byte` is boolean — rewrites `constraint_3_every_row`. -/
@[simp]
def boolean_use_first_byte (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.use_first_byte row * (1 - v.use_first_byte row) = 0

/-- `c_is_signed` is boolean — rewrites `constraint_4_every_row`. -/
@[simp]
def boolean_c_is_signed (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.c_is_signed row * (1 - v.c_is_signed row) = 0

/-- `b_op_or_sext = mode32 * (c_is_signed + 512 - b_op) + b_op` — linear
    identity defining the auxiliary opcode lookup column. Rewrites
    `constraint_5_every_row`. -/
@[simp]
def b_op_or_sext_def_holds (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.b_op_or_sext row
    - (v.mode32 row * (v.c_is_signed row + 512 - v.b_op row) + v.b_op row) = 0

/-- `mode32_and_c_is_signed = mode32 * c_is_signed`. Rewrites
    `constraint_6_every_row`. -/
@[simp]
def mode32_and_c_is_signed_def_holds (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  v.mode32_and_c_is_signed row - v.mode32 row * v.c_is_signed row = 0

/-- The seven F-typed every_row constraints bundled. Constraints 7–13
    (lookup-permutation interactions; mixed `F`/`ExtF`) are handled
    compositionally via `Airs/BinaryTable.lean`. -/
@[simp]
def core_every_row (v : Valid_Binary C F ExtF) (row : ℕ) : Prop :=
  boolean_mode32 v row
  ∧ boolean_carry_7 v row
  ∧ boolean_result_is_a v row
  ∧ boolean_use_first_byte v row
  ∧ boolean_c_is_signed v row
  ∧ b_op_or_sext_def_holds v row
  ∧ mode32_and_c_is_signed_def_holds v row

section extraction_bridge

@[simp]
lemma constraint_0_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_0_every_row v.circuit row ↔ boolean_mode32 v row := by
  unfold constraint_0_every_row boolean_mode32
  rw [v.mode32_def]

@[simp]
lemma constraint_1_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_1_every_row v.circuit row ↔ boolean_carry_7 v row := by
  unfold constraint_1_every_row boolean_carry_7
  rw [v.carry_7_def]

@[simp]
lemma constraint_2_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_2_every_row v.circuit row ↔ boolean_result_is_a v row := by
  unfold constraint_2_every_row boolean_result_is_a
  rw [v.result_is_a_def]

@[simp]
lemma constraint_3_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_3_every_row v.circuit row ↔ boolean_use_first_byte v row := by
  unfold constraint_3_every_row boolean_use_first_byte
  rw [v.use_first_byte_def]

@[simp]
lemma constraint_4_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_4_every_row v.circuit row ↔ boolean_c_is_signed v row := by
  unfold constraint_4_every_row boolean_c_is_signed
  rw [v.c_is_signed_def]

@[simp]
lemma constraint_5_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_5_every_row v.circuit row ↔ b_op_or_sext_def_holds v row := by
  unfold constraint_5_every_row b_op_or_sext_def_holds
  rw [v.b_op_or_sext_def, v.mode32_def, v.c_is_signed_def, v.b_op_def]

@[simp]
lemma constraint_6_of_extraction
    (v : Valid_Binary C F ExtF) (row : ℕ) :
    constraint_6_every_row v.circuit row ↔ mode32_and_c_is_signed_def_holds v row := by
  unfold constraint_6_every_row mode32_and_c_is_signed_def_holds
  rw [v.mode32_and_c_is_signed_def, v.mode32_def, v.c_is_signed_def]

end extraction_bridge

end ZiskFv.Airs.Binary
