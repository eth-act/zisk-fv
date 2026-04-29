import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.MemAlignReadByte

/-!
Named-column mirror of the extracted ZisK `MemAlignReadByte` AIR (pilout idx 7).

The `MemAlignReadByte` AIR is the read-only specialization of the
unaligned-access shim — it proves that a single-byte load decomposes
into one aligned 8-byte memory read plus a byte-level extraction. See
`vendor/zisk/state-machines/mem/pil/mem_align_byte.pil` (the `read==1,
write==0` branch).

Stage-1 columns (10 total):
  sel_high_4b (0), sel_high_2b (1), sel_high_b (2),
  direct_value (3), composed_value (4),
  value_16b (5), value_8b (6), byte_value (7),
  addr_w (8), step (9).

Stage-2 columns: gsum, im[0], im_high_degree[0].

F-typed constraints (4): boolean `sel_high_4b/2b/b` (0..2),
`composed_value` byte recombination (3).

Skipped (6): permutation interactions (4..9) — F/ExtF mixed.
-/

namespace ZiskFv.Airs.MemAlignReadByte

open Goldilocks
open MemAlignReadByte.extraction

/-- The shared "byte position" factor expression for read-byte. -/
@[simp]
def byte_value_factor {F : Type} [Field F] (sel_high_2b sel_high_b : F) : F :=
  16777216 * sel_high_2b * sel_high_b
  + 65536 * sel_high_2b * (1 - sel_high_b)
  + 256 * (1 - sel_high_2b) * sel_high_b
  + (1 - sel_high_2b) * (1 - sel_high_b)

@[simp]
def value_8b_factor {F : Type} [Field F] (sel_high_2b sel_high_b : F) : F :=
  16777216 * sel_high_2b * (1 - sel_high_b)
  + 65536 * sel_high_2b * sel_high_b
  + 256 * (1 - sel_high_2b) * (1 - sel_high_b)
  + (1 - sel_high_2b) * sel_high_b

@[simp]
def value_16b_factor {F : Type} [Field F] (sel_high_2b : F) : F :=
  65536 * (1 - sel_high_2b) + sel_high_2b

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Named accessors for one row of ZisK's `MemAlignReadByte` AIR. -/
structure Valid_MemAlignReadByte (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  sel_high_4b : ℕ → F
  sel_high_2b : ℕ → F
  sel_high_b : ℕ → F
  direct_value : ℕ → F
  composed_value : ℕ → F
  value_16b : ℕ → F
  value_8b : ℕ → F
  byte_value : ℕ → F
  addr_w : ℕ → F
  step : ℕ → F
  sel_high_4b_def : ∀ row,
    sel_high_4b row = Circuit.main circuit (id := 1) (column := 0) (row := row) (rotation := 0)
  sel_high_2b_def : ∀ row,
    sel_high_2b row = Circuit.main circuit (id := 1) (column := 1) (row := row) (rotation := 0)
  sel_high_b_def : ∀ row,
    sel_high_b row = Circuit.main circuit (id := 1) (column := 2) (row := row) (rotation := 0)
  direct_value_def : ∀ row,
    direct_value row = Circuit.main circuit (id := 1) (column := 3) (row := row) (rotation := 0)
  composed_value_def : ∀ row,
    composed_value row = Circuit.main circuit (id := 1) (column := 4) (row := row) (rotation := 0)
  value_16b_def : ∀ row,
    value_16b row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  value_8b_def : ∀ row,
    value_8b row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  byte_value_def : ∀ row,
    byte_value row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  addr_w_def : ∀ row,
    addr_w row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  step_def : ∀ row,
    step row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)

@[simp]
def boolean_sel_high_4b (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) : Prop :=
  v.sel_high_4b row * (1 - v.sel_high_4b row) = 0

@[simp]
def boolean_sel_high_2b (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) : Prop :=
  v.sel_high_2b row * (1 - v.sel_high_2b row) = 0

@[simp]
def boolean_sel_high_b (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) : Prop :=
  v.sel_high_b row * (1 - v.sel_high_b row) = 0

/-- `composed_value = byte_value * BVF + value_8b * V8F + value_16b * V16F`. -/
@[simp]
def composed_value_definition (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) : Prop :=
  v.composed_value row -
    (v.byte_value row * byte_value_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_8b row * value_8b_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_16b row * value_16b_factor (v.sel_high_2b row)) = 0

/-- All F-typed `every_row` constraints bundled. The six permutation
    interactions (4..9) skip-stub at the extraction layer. -/
@[simp]
def core_every_row (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) : Prop :=
  boolean_sel_high_4b v row
  ∧ boolean_sel_high_2b v row
  ∧ boolean_sel_high_b v row
  ∧ composed_value_definition v row

section extraction_bridge

@[simp]
lemma constraint_0_of_extraction (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) :
    constraint_0_every_row v.circuit row ↔ boolean_sel_high_4b v row := by
  unfold constraint_0_every_row boolean_sel_high_4b
  simp only [v.sel_high_4b_def]

@[simp]
lemma constraint_1_of_extraction (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) :
    constraint_1_every_row v.circuit row ↔ boolean_sel_high_2b v row := by
  unfold constraint_1_every_row boolean_sel_high_2b
  simp only [v.sel_high_2b_def]

@[simp]
lemma constraint_2_of_extraction (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) :
    constraint_2_every_row v.circuit row ↔ boolean_sel_high_b v row := by
  unfold constraint_2_every_row boolean_sel_high_b
  simp only [v.sel_high_b_def]

@[simp]
lemma constraint_3_of_extraction (v : Valid_MemAlignReadByte C F ExtF) (row : ℕ) :
    constraint_3_every_row v.circuit row ↔ composed_value_definition v row := by
  unfold constraint_3_every_row composed_value_definition
  simp only [v.sel_high_2b_def, v.sel_high_b_def, v.composed_value_def,
    v.byte_value_def, v.value_8b_def, v.value_16b_def,
    byte_value_factor, value_8b_factor, value_16b_factor]

end extraction_bridge

end ZiskFv.Airs.MemAlignReadByte
