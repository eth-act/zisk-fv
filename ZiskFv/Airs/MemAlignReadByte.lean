import Mathlib

import ZiskFv.Field.Goldilocks

/-!
Named-column mirror of the ZisK `MemAlignReadByte` AIR (pilout idx 7).

After the OpenVM Circuit retirement (Phase D), `Valid_MemAlignReadByte`
is a plain named-column record; the canonical AIR view is the Clean
`Air.Flat.Component` at `ZiskFv/AirsClean/MemAlignReadByte/`.

The `MemAlignReadByte` AIR is the read-only specialization of the
unaligned-access shim — it proves that a single-byte load decomposes
into one aligned 8-byte memory read plus a byte-level extraction. See
`zisk/state-machines/mem/pil/mem_align_byte.pil` (the `read==1,
write==0` branch).

Stage-1 columns (10 total):
  sel_high_4b (0), sel_high_2b (1), sel_high_b (2),
  direct_value (3), composed_value (4),
  value_16b (5), value_8b (6), byte_value (7),
  addr_w (8), step (9).

F-typed constraints (4): boolean `sel_high_4b/2b/b` (0..2),
`composed_value` byte recombination (3).
-/

namespace ZiskFv.Airs.MemAlignReadByte

open Goldilocks

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

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- Named accessors for one row of ZisK's `MemAlignReadByte` AIR. -/
structure Valid_MemAlignReadByte (F ExtF : Type) [Field F] [Field ExtF] where
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

@[simp]
def boolean_sel_high_4b (v : Valid_MemAlignReadByte F ExtF) (row : ℕ) : Prop :=
  v.sel_high_4b row * (1 - v.sel_high_4b row) = 0

@[simp]
def boolean_sel_high_2b (v : Valid_MemAlignReadByte F ExtF) (row : ℕ) : Prop :=
  v.sel_high_2b row * (1 - v.sel_high_2b row) = 0

@[simp]
def boolean_sel_high_b (v : Valid_MemAlignReadByte F ExtF) (row : ℕ) : Prop :=
  v.sel_high_b row * (1 - v.sel_high_b row) = 0

/-- `composed_value = byte_value * BVF + value_8b * V8F + value_16b * V16F`. -/
@[simp]
def composed_value_definition (v : Valid_MemAlignReadByte F ExtF) (row : ℕ) : Prop :=
  v.composed_value row -
    (v.byte_value row * byte_value_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_8b row * value_8b_factor (v.sel_high_2b row) (v.sel_high_b row)
     + v.value_16b row * value_16b_factor (v.sel_high_2b row)) = 0

/-- All F-typed `every_row` constraints bundled. The six permutation
    interactions (4..9) skip-stub at the extraction layer. -/
@[simp]
def core_every_row (v : Valid_MemAlignReadByte F ExtF) (row : ℕ) : Prop :=
  boolean_sel_high_4b v row
  ∧ boolean_sel_high_2b v row
  ∧ boolean_sel_high_b v row
  ∧ composed_value_definition v row

end ZiskFv.Airs.MemAlignReadByte
