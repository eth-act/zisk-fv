import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.MemAlignWriteByte

/-!
Named-column mirror of the extracted ZisK `MemAlignWriteByte` AIR
(pilout idx 8).

The `MemAlignWriteByte` AIR is the write-only specialization of the
unaligned-access shim — it proves that a single-byte store decomposes
into one aligned 8-byte memory read followed by an aligned 8-byte
memory write that updates only the targeted byte. See
`zisk/state-machines/mem/pil/mem_align_byte.pil` (the `read==0,
write==1` branch).

Stage-1 columns (14 total):
  sel_high_4b (0), sel_high_2b (1), sel_high_b (2),
  direct_value (3), composed_value (4),
  written_composed_value (5), written_byte_value (6),
  value_16b (7), value_8b (8), byte_value (9),
  addr_w (10), step (11),
  mem_write_values[0..1] (12..13).

Stage-2 columns: gsum, im[0..1], im_high_degree[0].

F-typed constraints (7): boolean `sel_high_4b/2b/b` (0..2),
`composed_value` byte recombination (3), `written_composed_value` byte
recombination (4), `mem_write_values[0]/[1]` recombination (5, 6).

Skipped (8): permutation interactions (7..14) — F/ExtF mixed.
-/

namespace ZiskFv.Airs.MemAlignWriteByte

open Goldilocks
open MemAlignWriteByte.extraction

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

/-- Named accessors for one row of ZisK's `MemAlignWriteByte` AIR. -/
structure Valid_MemAlignWriteByte (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  sel_high_4b : ℕ → F
  sel_high_2b : ℕ → F
  sel_high_b : ℕ → F
  direct_value : ℕ → F
  composed_value : ℕ → F
  written_composed_value : ℕ → F
  written_byte_value : ℕ → F
  value_16b : ℕ → F
  value_8b : ℕ → F
  byte_value : ℕ → F
  addr_w : ℕ → F
  step : ℕ → F
  mem_write_values_0 : ℕ → F
  mem_write_values_1 : ℕ → F
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
  written_composed_value_def : ∀ row,
    written_composed_value row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  written_byte_value_def : ∀ row,
    written_byte_value row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  value_16b_def : ∀ row,
    value_16b row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  value_8b_def : ∀ row,
    value_8b row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  byte_value_def : ∀ row,
    byte_value row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  addr_w_def : ∀ row,
    addr_w row = Circuit.main circuit (id := 1) (column := 10) (row := row) (rotation := 0)
  step_def : ∀ row,
    step row = Circuit.main circuit (id := 1) (column := 11) (row := row) (rotation := 0)
  mem_write_values_0_def : ∀ row,
    mem_write_values_0 row = Circuit.main circuit (id := 1) (column := 12) (row := row) (rotation := 0)
  mem_write_values_1_def : ∀ row,
    mem_write_values_1 row = Circuit.main circuit (id := 1) (column := 13) (row := row) (rotation := 0)

@[simp]
def boolean_sel_high_4b (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.sel_high_4b row * (1 - v.sel_high_4b row) = 0

@[simp]
def boolean_sel_high_2b (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.sel_high_2b row * (1 - v.sel_high_2b row) = 0

@[simp]
def boolean_sel_high_b (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.sel_high_b row * (1 - v.sel_high_b row) = 0

@[simp]
def composed_value_definition (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.composed_value row -
    (v.byte_value row * byte_value_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_8b row * value_8b_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_16b row * value_16b_factor (v.sel_high_2b row)) = 0

@[simp]
def written_composed_value_definition (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.written_composed_value row -
    (v.written_byte_value row * byte_value_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_8b row * value_8b_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_16b row * value_16b_factor (v.sel_high_2b row)) = 0

@[simp]
def mem_write_values_0_definition (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.mem_write_values_0 row -
    (v.sel_high_4b row * (v.direct_value row - v.written_composed_value row)
     + v.written_composed_value row) = 0

@[simp]
def mem_write_values_1_definition (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  v.mem_write_values_1 row -
    (v.sel_high_4b row * (v.written_composed_value row - v.direct_value row)
     + v.direct_value row) = 0

/-- All F-typed `every_row` constraints bundled. The eight permutation
    interactions (7..14) skip-stub at the extraction layer. -/
@[simp]
def core_every_row (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) : Prop :=
  boolean_sel_high_4b v row
  ∧ boolean_sel_high_2b v row
  ∧ boolean_sel_high_b v row
  ∧ composed_value_definition v row
  ∧ written_composed_value_definition v row
  ∧ mem_write_values_0_definition v row
  ∧ mem_write_values_1_definition v row

section extraction_bridge

@[simp]
lemma constraint_0_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_0_every_row v.circuit row ↔ boolean_sel_high_4b v row := by
  unfold constraint_0_every_row boolean_sel_high_4b
  simp only [v.sel_high_4b_def]

@[simp]
lemma constraint_1_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_1_every_row v.circuit row ↔ boolean_sel_high_2b v row := by
  unfold constraint_1_every_row boolean_sel_high_2b
  simp only [v.sel_high_2b_def]

@[simp]
lemma constraint_2_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_2_every_row v.circuit row ↔ boolean_sel_high_b v row := by
  unfold constraint_2_every_row boolean_sel_high_b
  simp only [v.sel_high_b_def]

@[simp]
lemma constraint_3_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_3_every_row v.circuit row ↔ composed_value_definition v row := by
  unfold constraint_3_every_row composed_value_definition
  simp only [v.sel_high_2b_def, v.sel_high_b_def, v.composed_value_def,
    v.byte_value_def, v.value_8b_def, v.value_16b_def,
    byte_value_factor, value_8b_factor, value_16b_factor]

@[simp]
lemma constraint_4_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_4_every_row v.circuit row ↔ written_composed_value_definition v row := by
  unfold constraint_4_every_row written_composed_value_definition
  simp only [v.sel_high_2b_def, v.sel_high_b_def, v.written_composed_value_def,
    v.written_byte_value_def, v.value_8b_def, v.value_16b_def,
    byte_value_factor, value_8b_factor, value_16b_factor]

@[simp]
lemma constraint_5_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_5_every_row v.circuit row ↔ mem_write_values_0_definition v row := by
  unfold constraint_5_every_row mem_write_values_0_definition
  simp only [v.sel_high_4b_def, v.direct_value_def,
    v.written_composed_value_def, v.mem_write_values_0_def]

@[simp]
lemma constraint_6_of_extraction (v : Valid_MemAlignWriteByte C F ExtF) (row : ℕ) :
    constraint_6_every_row v.circuit row ↔ mem_write_values_1_definition v row := by
  unfold constraint_6_every_row mem_write_values_1_definition
  simp only [v.sel_high_4b_def, v.direct_value_def,
    v.written_composed_value_def, v.mem_write_values_1_def]

end extraction_bridge

end ZiskFv.Airs.MemAlignWriteByte
