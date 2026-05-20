import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import Extraction.Binary

/-!
Named-column mirror of the extracted ZisK `Binary` AIR (pilout idx 10).

Mirrors `Airs/Binary/BinaryAdd.lean`. Only the seven F-typed constraints
(0..6) are exposed as named predicates here; constraints 7–13 are
skipped at the extraction layer because they mix `F` (witness cells)
with `ExtF` (challenges) — those are the lookup-permutation
interactions and are handled compositionally via
`Airs/BinaryTable.lean`'s `bin_table_consumer_wf` axiom.

Post-Phase-F1: the `circuit` field, all `_def` fields, the
`(C : Type → Type → Type) [Circuit F ExtF C]` parameter block, and the
`constraint_N_of_extraction` bridge lemmas have been retired. The
canonical AIR view is the Clean `Air.Flat.Component` at
`ZiskFv/AirsClean/Binary/`; the v1 named predicates `core_every_row` /
`boolean_*` remain as compositional inputs to downstream provers (e.g.
`Equivalence_v1/Bridge/Binary.lean::h_bool_c7`).
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
structure Valid_Binary (F ExtF : Type)
    [Field F] [Field ExtF] where
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

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- `mode32` is boolean — mirrors `constraint_0_every_row`. -/
@[simp]
def boolean_mode32 (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.mode32 row * (1 - v.mode32 row) = 0

/-- `carry[7]` is boolean — mirrors `constraint_1_every_row`. -/
@[simp]
def boolean_carry_7 (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.carry_7 row * (1 - v.carry_7 row) = 0

/-- `result_is_a` is boolean — mirrors `constraint_2_every_row`. -/
@[simp]
def boolean_result_is_a (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.result_is_a row * (1 - v.result_is_a row) = 0

/-- `use_first_byte` is boolean — mirrors `constraint_3_every_row`. -/
@[simp]
def boolean_use_first_byte (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.use_first_byte row * (1 - v.use_first_byte row) = 0

/-- `c_is_signed` is boolean — mirrors `constraint_4_every_row`. -/
@[simp]
def boolean_c_is_signed (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.c_is_signed row * (1 - v.c_is_signed row) = 0

/-- `b_op_or_sext = mode32 * (c_is_signed + 512 - b_op) + b_op` — linear
    identity defining the auxiliary opcode lookup column. Mirrors
    `constraint_5_every_row`. -/
@[simp]
def b_op_or_sext_def_holds (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.b_op_or_sext row
    - (v.mode32 row * (v.c_is_signed row + 512 - v.b_op row) + v.b_op row) = 0

/-- `mode32_and_c_is_signed = mode32 * c_is_signed`. Mirrors
    `constraint_6_every_row`. -/
@[simp]
def mode32_and_c_is_signed_def_holds (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  v.mode32_and_c_is_signed row - v.mode32 row * v.c_is_signed row = 0

/-- The seven F-typed every_row constraints bundled. Constraints 7–13
    (lookup-permutation interactions; mixed `F`/`ExtF`) are handled
    compositionally via `Airs/BinaryTable.lean`. -/
@[simp]
def core_every_row (v : Valid_Binary F ExtF) (row : ℕ) : Prop :=
  boolean_mode32 v row
  ∧ boolean_carry_7 v row
  ∧ boolean_result_is_a v row
  ∧ boolean_use_first_byte v row
  ∧ boolean_c_is_signed v row
  ∧ b_op_or_sext_def_holds v row
  ∧ mode32_and_c_is_signed_def_holds v row

end ZiskFv.Airs.Binary
