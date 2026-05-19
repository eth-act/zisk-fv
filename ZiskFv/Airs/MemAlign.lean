import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import Extraction.MemAlign

/-!
Named-column mirror of the extracted ZisK `MemAlign` AIR (pilout idx 5).

The `MemAlign` AIR handles unaligned memory accesses by spanning multiple
aligned `Mem` rows. See `zisk/state-machines/mem/pil/mem_align.pil`
for the underlying PIL source.

Stage-1 columns (29 total):
  addr (0), offset (1), width (2), wr (3), pc (4), reset (5),
  sel_up_to_down (6), sel_down_to_up (7),
  reg[0..7] (8..15), sel[0..7] (16..23),
  step (24), delta_addr (25), sel_prove (26), value[0..1] (27..28).

Stage-2 columns (6 total):
  gsum (0), im[0..3] (1..4), im_extra (5).

F-typed constraints (25): rotated `reg`-continuity (1,3,5,7,9,11,13,15),
boot-row pc (16), sel binary (17..24), wr/reset/sel-up/sel-down binary
(25..28), delta_addr definition (29), sel_prove disjoint (30),
value[0]/value[1] reconstruction (31, 32).

Skipped (15): forward-rotated `reg`-continuity rows (0,2,4,6,8,10,12,14)
which use the unsupported positive `rowOffset = +1`, plus the seven
`gsum`/permutation interactions (33..39) that mix F and ExtF.

Bridge lemmas claim only what the AIR directly enforces — no semantics
beyond the row-local constraint.
-/

namespace ZiskFv.Airs.MemAlign

open Goldilocks
open MemAlign.extraction

/-- Named accessors for one row of ZisK's `MemAlign` AIR. -/
structure Valid_MemAlign (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  addr : ℕ → F
  offset : ℕ → F
  width : ℕ → F
  wr : ℕ → F
  pc : ℕ → F
  reset : ℕ → F
  sel_up_to_down : ℕ → F
  sel_down_to_up : ℕ → F
  reg_0 : ℕ → F
  reg_1 : ℕ → F
  reg_2 : ℕ → F
  reg_3 : ℕ → F
  reg_4 : ℕ → F
  reg_5 : ℕ → F
  reg_6 : ℕ → F
  reg_7 : ℕ → F
  sel_0 : ℕ → F
  sel_1 : ℕ → F
  sel_2 : ℕ → F
  sel_3 : ℕ → F
  sel_4 : ℕ → F
  sel_5 : ℕ → F
  sel_6 : ℕ → F
  sel_7 : ℕ → F
  step : ℕ → F
  delta_addr : ℕ → F
  sel_prove : ℕ → F
  value_0 : ℕ → F
  value_1 : ℕ → F
  /-- The first preprocessed column (`L1`) used by constraint 16. -/
  preL1 : ℕ → F
  addr_def : ∀ row,
    addr row = Circuit.main circuit (id := 1) (column := 0) (row := row) (rotation := 0)
  offset_def : ∀ row,
    offset row = Circuit.main circuit (id := 1) (column := 1) (row := row) (rotation := 0)
  width_def : ∀ row,
    width row = Circuit.main circuit (id := 1) (column := 2) (row := row) (rotation := 0)
  wr_def : ∀ row,
    wr row = Circuit.main circuit (id := 1) (column := 3) (row := row) (rotation := 0)
  pc_def : ∀ row,
    pc row = Circuit.main circuit (id := 1) (column := 4) (row := row) (rotation := 0)
  reset_def : ∀ row,
    reset row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  sel_up_to_down_def : ∀ row,
    sel_up_to_down row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  sel_down_to_up_def : ∀ row,
    sel_down_to_up row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  reg_0_def : ∀ row,
    reg_0 row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  reg_1_def : ∀ row,
    reg_1 row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  reg_2_def : ∀ row,
    reg_2 row = Circuit.main circuit (id := 1) (column := 10) (row := row) (rotation := 0)
  reg_3_def : ∀ row,
    reg_3 row = Circuit.main circuit (id := 1) (column := 11) (row := row) (rotation := 0)
  reg_4_def : ∀ row,
    reg_4 row = Circuit.main circuit (id := 1) (column := 12) (row := row) (rotation := 0)
  reg_5_def : ∀ row,
    reg_5 row = Circuit.main circuit (id := 1) (column := 13) (row := row) (rotation := 0)
  reg_6_def : ∀ row,
    reg_6 row = Circuit.main circuit (id := 1) (column := 14) (row := row) (rotation := 0)
  reg_7_def : ∀ row,
    reg_7 row = Circuit.main circuit (id := 1) (column := 15) (row := row) (rotation := 0)
  sel_0_def : ∀ row,
    sel_0 row = Circuit.main circuit (id := 1) (column := 16) (row := row) (rotation := 0)
  sel_1_def : ∀ row,
    sel_1 row = Circuit.main circuit (id := 1) (column := 17) (row := row) (rotation := 0)
  sel_2_def : ∀ row,
    sel_2 row = Circuit.main circuit (id := 1) (column := 18) (row := row) (rotation := 0)
  sel_3_def : ∀ row,
    sel_3 row = Circuit.main circuit (id := 1) (column := 19) (row := row) (rotation := 0)
  sel_4_def : ∀ row,
    sel_4 row = Circuit.main circuit (id := 1) (column := 20) (row := row) (rotation := 0)
  sel_5_def : ∀ row,
    sel_5 row = Circuit.main circuit (id := 1) (column := 21) (row := row) (rotation := 0)
  sel_6_def : ∀ row,
    sel_6 row = Circuit.main circuit (id := 1) (column := 22) (row := row) (rotation := 0)
  sel_7_def : ∀ row,
    sel_7 row = Circuit.main circuit (id := 1) (column := 23) (row := row) (rotation := 0)
  step_def : ∀ row,
    step row = Circuit.main circuit (id := 1) (column := 24) (row := row) (rotation := 0)
  delta_addr_def : ∀ row,
    delta_addr row = Circuit.main circuit (id := 1) (column := 25) (row := row) (rotation := 0)
  sel_prove_def : ∀ row,
    sel_prove row = Circuit.main circuit (id := 1) (column := 26) (row := row) (rotation := 0)
  value_0_def : ∀ row,
    value_0 row = Circuit.main circuit (id := 1) (column := 27) (row := row) (rotation := 0)
  value_1_def : ∀ row,
    value_1 row = Circuit.main circuit (id := 1) (column := 28) (row := row) (rotation := 0)
  preL1_def : ∀ row,
    preL1 row = Circuit.preprocessed circuit (column := 0) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Down-to-up `reg[i]` continuity: when `sel_down_to_up = 1` and `sel[i] = 1`,
    the previous row's `reg[i]` matches this row's. Rewrites
    `constraint_{1,3,5,7,9,11,13,15}_every_row` (per-lane). -/
@[simp]
def down_to_up_continuity_0 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_0 (row - 1) - v.reg_0 row) * v.sel_0 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_1 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_1 (row - 1) - v.reg_1 row) * v.sel_1 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_2 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_2 (row - 1) - v.reg_2 row) * v.sel_2 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_3 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_3 (row - 1) - v.reg_3 row) * v.sel_3 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_4 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_4 (row - 1) - v.reg_4 row) * v.sel_4 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_5 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_5 (row - 1) - v.reg_5 row) * v.sel_5 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_6 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_6 (row - 1) - v.reg_6 row) * v.sel_6 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_7 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  (v.reg_7 (row - 1) - v.reg_7 row) * v.sel_7 row * v.sel_down_to_up row = 0

/-- The boot row's `pc` is zero (enforced by the `L1` selector). -/
@[simp]
def boot_pc_zero (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.preL1 row * v.pc row = 0

@[simp]
def boolean_sel_0 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_0 row * (1 - v.sel_0 row) = 0

@[simp]
def boolean_sel_1 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_1 row * (1 - v.sel_1 row) = 0

@[simp]
def boolean_sel_2 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_2 row * (1 - v.sel_2 row) = 0

@[simp]
def boolean_sel_3 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_3 row * (1 - v.sel_3 row) = 0

@[simp]
def boolean_sel_4 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_4 row * (1 - v.sel_4 row) = 0

@[simp]
def boolean_sel_5 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_5 row * (1 - v.sel_5 row) = 0

@[simp]
def boolean_sel_6 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_6 row * (1 - v.sel_6 row) = 0

@[simp]
def boolean_sel_7 (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_7 row * (1 - v.sel_7 row) = 0

@[simp]
def boolean_wr (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.wr row * (1 - v.wr row) = 0

@[simp]
def boolean_reset (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.reset row * (1 - v.reset row) = 0

@[simp]
def boolean_sel_up_to_down (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_up_to_down row * (1 - v.sel_up_to_down row) = 0

@[simp]
def boolean_sel_down_to_up (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_down_to_up row * (1 - v.sel_down_to_up row) = 0

/-- `delta_addr` is the gated forward-difference of `addr`. -/
@[simp]
def delta_addr_definition (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.delta_addr row - (v.addr row - v.addr (row - 1)) * (1 - v.reset row) = 0

/-- `sel_prove` and `sel_assume` (`sel_up_to_down + sel_down_to_up`)
    are disjoint. -/
@[simp]
def sel_prove_disjoint (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.sel_prove row * (v.sel_up_to_down row + v.sel_down_to_up row) = 0

/-- `value[0]` reconstruction: chooses between `sel_prove`'s rotated
    register-byte sum (8 cases keyed by `sel[0..7]`) and `sel_assume`'s
    direct low-32-bit recombination of `reg[0..3]`. -/
@[simp]
def value_0_reconstruction (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.value_0 row -
    (v.sel_prove row *
      (v.sel_0 row * (v.reg_0 row + v.reg_1 row * 256 + v.reg_2 row * 65536 + v.reg_3 row * 16777216)
       + v.sel_1 row * (v.reg_1 row + v.reg_2 row * 256 + v.reg_3 row * 65536 + v.reg_4 row * 16777216)
       + v.sel_2 row * (v.reg_2 row + v.reg_3 row * 256 + v.reg_4 row * 65536 + v.reg_5 row * 16777216)
       + v.sel_3 row * (v.reg_3 row + v.reg_4 row * 256 + v.reg_5 row * 65536 + v.reg_6 row * 16777216)
       + v.sel_4 row * (v.reg_4 row + v.reg_5 row * 256 + v.reg_6 row * 65536 + v.reg_7 row * 16777216)
       + v.sel_5 row * (v.reg_5 row + v.reg_6 row * 256 + v.reg_7 row * 65536 + v.reg_0 row * 16777216)
       + v.sel_6 row * (v.reg_6 row + v.reg_7 row * 256 + v.reg_0 row * 65536 + v.reg_1 row * 16777216)
       + v.sel_7 row * (v.reg_7 row + v.reg_0 row * 256 + v.reg_1 row * 65536 + v.reg_2 row * 16777216))
     + (v.sel_up_to_down row + v.sel_down_to_up row)
       * (v.reg_0 row + v.reg_1 row * 256 + v.reg_2 row * 65536 + v.reg_3 row * 16777216)) = 0

/-- `value[1]` reconstruction: dual of `value_0_reconstruction` for the
    high lane (cycles starting at `reg[4]`). -/
@[simp]
def value_1_reconstruction (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  v.value_1 row -
    (v.sel_prove row *
      (v.sel_0 row * (v.reg_4 row + v.reg_5 row * 256 + v.reg_6 row * 65536 + v.reg_7 row * 16777216)
       + v.sel_1 row * (v.reg_5 row + v.reg_6 row * 256 + v.reg_7 row * 65536 + v.reg_0 row * 16777216)
       + v.sel_2 row * (v.reg_6 row + v.reg_7 row * 256 + v.reg_0 row * 65536 + v.reg_1 row * 16777216)
       + v.sel_3 row * (v.reg_7 row + v.reg_0 row * 256 + v.reg_1 row * 65536 + v.reg_2 row * 16777216)
       + v.sel_4 row * (v.reg_0 row + v.reg_1 row * 256 + v.reg_2 row * 65536 + v.reg_3 row * 16777216)
       + v.sel_5 row * (v.reg_1 row + v.reg_2 row * 256 + v.reg_3 row * 65536 + v.reg_4 row * 16777216)
       + v.sel_6 row * (v.reg_2 row + v.reg_3 row * 256 + v.reg_4 row * 65536 + v.reg_5 row * 16777216)
       + v.sel_7 row * (v.reg_3 row + v.reg_4 row * 256 + v.reg_5 row * 65536 + v.reg_6 row * 16777216))
     + (v.sel_up_to_down row + v.sel_down_to_up row)
       * (v.reg_4 row + v.reg_5 row * 256 + v.reg_6 row * 65536 + v.reg_7 row * 16777216)) = 0

/-- All F-typed `every_row` constraints bundled. The forward-rotated
    `reg`-continuity siblings (constraints 0,2,4,6,8,10,12,14) and the
    `gsum`/permutation interactions (33..39) are skipped at extraction;
    the compositional proof passes those through to the OperationBus /
    MemoryBus models. -/
@[simp]
def core_every_row (v : Valid_MemAlign C F ExtF) (row : ℕ) : Prop :=
  down_to_up_continuity_0 v row
  ∧ down_to_up_continuity_1 v row
  ∧ down_to_up_continuity_2 v row
  ∧ down_to_up_continuity_3 v row
  ∧ down_to_up_continuity_4 v row
  ∧ down_to_up_continuity_5 v row
  ∧ down_to_up_continuity_6 v row
  ∧ down_to_up_continuity_7 v row
  ∧ boot_pc_zero v row
  ∧ boolean_sel_0 v row
  ∧ boolean_sel_1 v row
  ∧ boolean_sel_2 v row
  ∧ boolean_sel_3 v row
  ∧ boolean_sel_4 v row
  ∧ boolean_sel_5 v row
  ∧ boolean_sel_6 v row
  ∧ boolean_sel_7 v row
  ∧ boolean_wr v row
  ∧ boolean_reset v row
  ∧ boolean_sel_up_to_down v row
  ∧ boolean_sel_down_to_up v row
  ∧ delta_addr_definition v row
  ∧ sel_prove_disjoint v row
  ∧ value_0_reconstruction v row
  ∧ value_1_reconstruction v row

section extraction_bridge

@[simp]
lemma constraint_1_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_1_every_row v.circuit row ↔ down_to_up_continuity_0 v row := by
  unfold constraint_1_every_row down_to_up_continuity_0
  simp only [v.reg_0_def, v.sel_0_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_3_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_3_every_row v.circuit row ↔ down_to_up_continuity_1 v row := by
  unfold constraint_3_every_row down_to_up_continuity_1
  simp only [v.reg_1_def, v.sel_1_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_5_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_5_every_row v.circuit row ↔ down_to_up_continuity_2 v row := by
  unfold constraint_5_every_row down_to_up_continuity_2
  simp only [v.reg_2_def, v.sel_2_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_7_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_7_every_row v.circuit row ↔ down_to_up_continuity_3 v row := by
  unfold constraint_7_every_row down_to_up_continuity_3
  simp only [v.reg_3_def, v.sel_3_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_9_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_9_every_row v.circuit row ↔ down_to_up_continuity_4 v row := by
  unfold constraint_9_every_row down_to_up_continuity_4
  simp only [v.reg_4_def, v.sel_4_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_11_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_11_every_row v.circuit row ↔ down_to_up_continuity_5 v row := by
  unfold constraint_11_every_row down_to_up_continuity_5
  simp only [v.reg_5_def, v.sel_5_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_13_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_13_every_row v.circuit row ↔ down_to_up_continuity_6 v row := by
  unfold constraint_13_every_row down_to_up_continuity_6
  simp only [v.reg_6_def, v.sel_6_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_15_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_15_every_row v.circuit row ↔ down_to_up_continuity_7 v row := by
  unfold constraint_15_every_row down_to_up_continuity_7
  simp only [v.reg_7_def, v.sel_7_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_16_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_16_every_row v.circuit row ↔ boot_pc_zero v row := by
  unfold constraint_16_every_row boot_pc_zero
  rw [v.preL1_def, v.pc_def]

@[simp]
lemma constraint_17_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_17_every_row v.circuit row ↔ boolean_sel_0 v row := by
  unfold constraint_17_every_row boolean_sel_0
  rw [v.sel_0_def]

@[simp]
lemma constraint_18_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_18_every_row v.circuit row ↔ boolean_sel_1 v row := by
  unfold constraint_18_every_row boolean_sel_1
  rw [v.sel_1_def]

@[simp]
lemma constraint_19_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_19_every_row v.circuit row ↔ boolean_sel_2 v row := by
  unfold constraint_19_every_row boolean_sel_2
  rw [v.sel_2_def]

@[simp]
lemma constraint_20_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_20_every_row v.circuit row ↔ boolean_sel_3 v row := by
  unfold constraint_20_every_row boolean_sel_3
  rw [v.sel_3_def]

@[simp]
lemma constraint_21_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_21_every_row v.circuit row ↔ boolean_sel_4 v row := by
  unfold constraint_21_every_row boolean_sel_4
  rw [v.sel_4_def]

@[simp]
lemma constraint_22_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_22_every_row v.circuit row ↔ boolean_sel_5 v row := by
  unfold constraint_22_every_row boolean_sel_5
  rw [v.sel_5_def]

@[simp]
lemma constraint_23_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_23_every_row v.circuit row ↔ boolean_sel_6 v row := by
  unfold constraint_23_every_row boolean_sel_6
  rw [v.sel_6_def]

@[simp]
lemma constraint_24_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_24_every_row v.circuit row ↔ boolean_sel_7 v row := by
  unfold constraint_24_every_row boolean_sel_7
  rw [v.sel_7_def]

@[simp]
lemma constraint_25_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_25_every_row v.circuit row ↔ boolean_wr v row := by
  unfold constraint_25_every_row boolean_wr
  rw [v.wr_def]

@[simp]
lemma constraint_26_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_26_every_row v.circuit row ↔ boolean_reset v row := by
  unfold constraint_26_every_row boolean_reset
  rw [v.reset_def]

@[simp]
lemma constraint_27_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_27_every_row v.circuit row ↔ boolean_sel_up_to_down v row := by
  unfold constraint_27_every_row boolean_sel_up_to_down
  rw [v.sel_up_to_down_def]

@[simp]
lemma constraint_28_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_28_every_row v.circuit row ↔ boolean_sel_down_to_up v row := by
  unfold constraint_28_every_row boolean_sel_down_to_up
  rw [v.sel_down_to_up_def]

@[simp]
lemma constraint_29_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_29_every_row v.circuit row ↔ delta_addr_definition v row := by
  unfold constraint_29_every_row delta_addr_definition
  simp only [v.addr_def, v.delta_addr_def, v.reset_def]

@[simp]
lemma constraint_30_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_30_every_row v.circuit row ↔ sel_prove_disjoint v row := by
  unfold constraint_30_every_row sel_prove_disjoint
  rw [v.sel_prove_def, v.sel_up_to_down_def, v.sel_down_to_up_def]

@[simp]
lemma constraint_31_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_31_every_row v.circuit row ↔ value_0_reconstruction v row := by
  unfold constraint_31_every_row value_0_reconstruction
  rw [v.value_0_def, v.sel_prove_def, v.sel_up_to_down_def, v.sel_down_to_up_def,
      v.sel_0_def, v.sel_1_def, v.sel_2_def, v.sel_3_def,
      v.sel_4_def, v.sel_5_def, v.sel_6_def, v.sel_7_def,
      v.reg_0_def, v.reg_1_def, v.reg_2_def, v.reg_3_def,
      v.reg_4_def, v.reg_5_def, v.reg_6_def, v.reg_7_def]

@[simp]
lemma constraint_32_of_extraction (v : Valid_MemAlign C F ExtF) (row : ℕ) :
    constraint_32_every_row v.circuit row ↔ value_1_reconstruction v row := by
  unfold constraint_32_every_row value_1_reconstruction
  rw [v.value_1_def, v.sel_prove_def, v.sel_up_to_down_def, v.sel_down_to_up_def,
      v.sel_0_def, v.sel_1_def, v.sel_2_def, v.sel_3_def,
      v.sel_4_def, v.sel_5_def, v.sel_6_def, v.sel_7_def,
      v.reg_0_def, v.reg_1_def, v.reg_2_def, v.reg_3_def,
      v.reg_4_def, v.reg_5_def, v.reg_6_def, v.reg_7_def]

end extraction_bridge

end ZiskFv.Airs.MemAlign
