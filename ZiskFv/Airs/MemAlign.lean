import Mathlib

import ZiskFv.Field.Goldilocks

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

/-- Named accessors for one row of ZisK's `MemAlign` AIR. -/
structure Valid_MemAlign (F ExtF : Type) [Field F] [Field ExtF] where
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

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- Down-to-up `reg[i]` continuity: when `sel_down_to_up = 1` and `sel[i] = 1`,
    the previous row's `reg[i]` matches this row's. Rewrites
    `constraint_{1,3,5,7,9,11,13,15}_every_row` (per-lane). -/
@[simp]
def down_to_up_continuity_0 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_0 (row - 1) - v.reg_0 row) * v.sel_0 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_1 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_1 (row - 1) - v.reg_1 row) * v.sel_1 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_2 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_2 (row - 1) - v.reg_2 row) * v.sel_2 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_3 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_3 (row - 1) - v.reg_3 row) * v.sel_3 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_4 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_4 (row - 1) - v.reg_4 row) * v.sel_4 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_5 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_5 (row - 1) - v.reg_5 row) * v.sel_5 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_6 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_6 (row - 1) - v.reg_6 row) * v.sel_6 row * v.sel_down_to_up row = 0

@[simp]
def down_to_up_continuity_7 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  (v.reg_7 (row - 1) - v.reg_7 row) * v.sel_7 row * v.sel_down_to_up row = 0

/-- The boot row's `pc` is zero (enforced by the `L1` selector). -/
@[simp]
def boot_pc_zero (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.preL1 row * v.pc row = 0

@[simp]
def boolean_sel_0 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_0 row * (1 - v.sel_0 row) = 0

@[simp]
def boolean_sel_1 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_1 row * (1 - v.sel_1 row) = 0

@[simp]
def boolean_sel_2 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_2 row * (1 - v.sel_2 row) = 0

@[simp]
def boolean_sel_3 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_3 row * (1 - v.sel_3 row) = 0

@[simp]
def boolean_sel_4 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_4 row * (1 - v.sel_4 row) = 0

@[simp]
def boolean_sel_5 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_5 row * (1 - v.sel_5 row) = 0

@[simp]
def boolean_sel_6 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_6 row * (1 - v.sel_6 row) = 0

@[simp]
def boolean_sel_7 (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_7 row * (1 - v.sel_7 row) = 0

@[simp]
def boolean_wr (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.wr row * (1 - v.wr row) = 0

@[simp]
def boolean_reset (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.reset row * (1 - v.reset row) = 0

@[simp]
def boolean_sel_up_to_down (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_up_to_down row * (1 - v.sel_up_to_down row) = 0

@[simp]
def boolean_sel_down_to_up (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_down_to_up row * (1 - v.sel_down_to_up row) = 0

/-- `delta_addr` is the gated forward-difference of `addr`. -/
@[simp]
def delta_addr_definition (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.delta_addr row - (v.addr row - v.addr (row - 1)) * (1 - v.reset row) = 0

/-- `sel_prove` and `sel_assume` (`sel_up_to_down + sel_down_to_up`)
    are disjoint. -/
@[simp]
def sel_prove_disjoint (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
  v.sel_prove row * (v.sel_up_to_down row + v.sel_down_to_up row) = 0

/-- `value[0]` reconstruction: chooses between `sel_prove`'s rotated
    register-byte sum (8 cases keyed by `sel[0..7]`) and `sel_assume`'s
    direct low-32-bit recombination of `reg[0..3]`. -/
@[simp]
def value_0_reconstruction (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
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
def value_1_reconstruction (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
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
def core_every_row (v : Valid_MemAlign F ExtF) (row : ℕ) : Prop :=
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

end ZiskFv.Airs.MemAlign
