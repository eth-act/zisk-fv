import Mathlib

import ZiskFv.Field.Goldilocks

/-!
Named-column mirror of the ZisK `Mem` AIR (pilout idx 2).

After the OpenVM Circuit retirement (Phase D), `Valid_Mem` is a plain
named-column record; the canonical AIR view is the Clean
`Air.Flat.Component` at `ZiskFv/AirsClean/Mem/`.

The nine F-typed constraints (3, 4, 5, 6, 7, 8, 18, 21, 23) are named as the
local `core_every_row` surface consumed by the current Clean bridge. The
generated extractor now also emits the mixed segment/permutation constraints;
this module starts naming their source-level counterparts using explicit
segment/challenge columns. The global replay proof still has to consume those
facts to derive chronological memory-state soundness.

The F-typed surface bridged here covers the per-row local invariants
of the `Mem` AIR's primary witness columns: booleanity of `sel`,
`sel_dual`, `addr_changes`, `wr`; the `wr ⇒ sel` and `sel_dual ⇒ sel`
implications (encoded as products); the `read_same_addr` definitional
identity; and the "address change without write zeros the value"
constraints. Continuity (cross-row) constraints involve segment carry columns
and permutation accumulators. They are exposed separately rather than folded
into the local row `Spec`.

Column layout taken from the witness-column header in
`ZiskFv/ZiskFv/Extraction/Mem.lean`. Stage-1 columns:
* 0: `addr`
* 1: `step`
* 2: `sel`
* 3: `addr_changes`
* 4: `step_dual`
* 5: `sel_dual`
* 6: `value[0]`
* 7: `value[1]`
* 8: `wr`
* 9: `previous_step`
* 10: `l_increment`
* 11: `h_increment`
* 12: `read_same_addr`
Stage-2 columns:
* 0: `gsum`
* 1: `im[0]`
* 2: `im[1]`
-/

namespace ZiskFv.Airs.Mem

open Goldilocks

/-- Named accessors for one row of ZisK's `Mem` AIR. -/
structure Valid_Mem (F ExtF : Type) [Field F] [Field ExtF] where
  /-- Memory address of this entry (mem-byte address; multiplied by `bytes`
      before being sent to the bus). -/
  addr : ℕ → F
  /-- Mem-step (timestamp) of this entry. -/
  step : ℕ → F
  /-- Selector — boolean: `1` if this row is "live" (sent to bus). -/
  sel : ℕ → F
  /-- Whether this row's `addr` differs from the previous row's `addr`. -/
  addr_changes : ℕ → F
  /-- Dual-mode second-step (only meaningful if `sel_dual = 1`). -/
  step_dual : ℕ → F
  /-- Dual-mode selector — boolean: `1` if this row carries a second
      operation at the same address. -/
  sel_dual : ℕ → F
  /-- Low-32-bit chunk of the 64-bit memory value. -/
  value_0 : ℕ → F
  /-- High-32-bit chunk of the 64-bit memory value. -/
  value_1 : ℕ → F
  /-- Write flag — boolean: `1` for store, `0` for load. -/
  wr : ℕ → F
  /-- Previous-step witness column (mutable-mem variant). -/
  previous_step : ℕ → F
  /-- Low chunk of the address/step combined increment. -/
  increment_0 : ℕ → F
  /-- High chunk of the address/step combined increment. -/
  increment_1 : ℕ → F
  /-- `read_same_addr = (1 - addr_changes) * (1 - wr)` — boolean witness. -/
  read_same_addr : ℕ → F
  /-- Stage-2 permutation accumulator (`gsum`). -/
  gsum : ℕ → F
  im_0 : ℕ → F
  im_1 : ℕ → F

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- `sel_dual` is boolean. -/
@[simp]
def boolean_sel_dual (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  v.sel_dual row * (1 - v.sel_dual row) = 0

/-- `sel_dual` requires `sel`.
    Encoded multiplicatively as `(1 - sel) * sel_dual = 0`. -/
@[simp]
def sel_dual_implies_sel (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  (1 - v.sel row) * v.sel_dual row = 0

/-- `sel` is boolean. -/
@[simp]
def boolean_sel (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  v.sel row * (1 - v.sel row) = 0

/-- `addr_changes` is boolean. -/
@[simp]
def boolean_addr_changes (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  v.addr_changes row * (1 - v.addr_changes row) = 0

/-- `wr` is boolean. -/
@[simp]
def boolean_wr (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  v.wr row * (1 - v.wr row) = 0

/-- All writes must be sent to the bus.
    Encoded as `wr * (1 - sel) = 0`. -/
@[simp]
def wr_implies_sel (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  v.wr row * (1 - v.sel row) = 0

/-- Definitional identity for `read_same_addr`. -/
@[simp]
def read_same_addr_def_eq (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  v.read_same_addr row - (1 - v.addr_changes row) * (1 - v.wr row) = 0

/-- Address change without write zeros the low value chunk. -/
@[simp]
def addr_change_no_write_zeros_value_0 (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  (v.addr_changes row * (1 - v.wr row)) * v.value_0 row = 0

/-- Address change without write zeros the high value chunk. -/
@[simp]
def addr_change_no_write_zeros_value_1 (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  (v.addr_changes row * (1 - v.wr row)) * v.value_1 row = 0

/-- The nine F-typed every-row constraints bundled. The remaining generated
    segment/permutation constraints are named separately below because they
    need full-trace context, not just one local `MemRow`. -/
@[simp]
def core_every_row (v : Valid_Mem F ExtF) (row : ℕ) : Prop :=
  boolean_sel_dual v row
  ∧ sel_dual_implies_sel v row
  ∧ boolean_sel v row
  ∧ boolean_addr_changes v row
  ∧ boolean_wr v row
  ∧ wr_implies_sel v row
  ∧ read_same_addr_def_eq v row
  ∧ addr_change_no_write_zeros_value_0 v row
  ∧ addr_change_no_write_zeros_value_1 v row

/-! ## Generated segment/continuity surface

The extractor emits constraints 0-23 as single-field formulas over witness,
exposed, and preprocessed Mem columns. `SegmentColumns` names the non-witness
columns needed for those formulas, while `segment_every_row` mirrors the
generated constraint order. Constraints 24-33 are the permutation accumulator
surface and will be bound in the next slice.
-/

/-- Non-witness Mem columns used by generated constraints 0-23. -/
structure SegmentColumns (F : Type) [Field F] where
  segment_id : F
  is_first_segment : F
  is_last_segment : F
  previous_segment_value_0 : F
  previous_segment_value_1 : F
  previous_segment_step : F
  previous_segment_addr : F
  segment_last_value_0 : F
  segment_last_value_1 : F
  segment_last_step : F
  segment_last_addr : F
  distance_base_0 : F
  distance_base_1 : F
  distance_end_0 : F
  distance_end_1 : F
  segment_l1 : ℕ → F

variable {F : Type} [Field F]

@[simp]
def previous_row_step (v : Valid_Mem F F) (row : ℕ) : F :=
  v.sel_dual (row - 1) * (v.step_dual (row - 1) - v.step (row - 1))
    + v.step (row - 1)

@[simp]
def segment_previous_addr
    (cols : SegmentColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  cols.segment_l1 row * (cols.previous_segment_addr - v.addr (row - 1))
    + v.addr (row - 1)

@[simp]
def segment_previous_value_0
    (cols : SegmentColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  cols.segment_l1 row * (cols.previous_segment_value_0 - v.value_0 (row - 1))
    + v.value_0 (row - 1)

@[simp]
def segment_previous_value_1
    (cols : SegmentColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  cols.segment_l1 row * (cols.previous_segment_value_1 - v.value_1 (row - 1))
    + v.value_1 (row - 1)

@[simp]
def delta_step (v : Valid_Mem F F) (row : ℕ) : F :=
  (v.step row - v.previous_step row) + (1 - v.wr row)

@[simp]
def delta_addr
    (cols : SegmentColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.addr row - segment_previous_addr cols v row

/-- Generated Mem constraints 0-23, excluding only the later permutation
accumulator constraints 24-33. -/
@[simp]
def segment_every_row
    (cols : SegmentColumns F) (v : Valid_Mem F F) (row : ℕ) : Prop :=
  cols.is_first_segment * (1 - cols.is_first_segment) = 0
  ∧ cols.is_last_segment * (1 - cols.is_last_segment) = 0
  ∧ cols.is_first_segment * cols.segment_id = 0
  ∧ v.sel_dual row * (1 - v.sel_dual row) = 0
  ∧ (1 - v.sel row) * v.sel_dual row = 0
  ∧ v.sel row * (1 - v.sel row) = 0
  ∧ v.addr_changes row * (1 - v.addr_changes row) = 0
  ∧ v.wr row * (1 - v.wr row) = 0
  ∧ v.wr row * (1 - v.sel row) = 0
  ∧ cols.segment_l1 (row + 1) *
      (v.value_0 row - cols.segment_last_value_0) = 0
  ∧ cols.segment_l1 (row + 1) *
      (v.value_1 row - cols.segment_last_value_1) = 0
  ∧ cols.segment_l1 (row + 1) *
      (v.addr row - cols.segment_last_addr) = 0
  ∧ cols.segment_l1 (row + 1) *
      (v.sel_dual row * (v.step_dual row - v.step row) + v.step row
        - cols.segment_last_step) = 0
  ∧ (cols.previous_segment_addr - 335544320)
      - (cols.distance_base_0 + 65536 * cols.distance_base_1) = 0
  ∧ (402653183 - cols.segment_last_addr)
      - (cols.distance_end_0 + 65536 * cols.distance_end_1) = 0
  ∧ v.previous_step row
      - (cols.segment_l1 row *
          (cols.previous_segment_step - previous_row_step v row)
        + previous_row_step v row) = 0
  ∧ (v.increment_0 row + 4194304 * v.increment_1 row + 1)
      - (v.addr_changes row * (delta_addr cols v row - delta_step v row)
        + delta_step v row) = 0
  ∧ (cols.is_first_segment * cols.segment_l1 row) *
      (1 - v.addr_changes row) = 0
  ∧ v.read_same_addr row
      - (1 - v.addr_changes row) * (1 - v.wr row) = 0
  ∧ (1 - v.addr_changes row) *
      (v.addr row - segment_previous_addr cols v row) = 0
  ∧ v.read_same_addr row *
      (v.value_0 row - segment_previous_value_0 cols v row) = 0
  ∧ (v.addr_changes row * (1 - v.wr row)) * v.value_0 row = 0
  ∧ v.read_same_addr row *
      (v.value_1 row - segment_previous_value_1 cols v row) = 0
  ∧ (v.addr_changes row * (1 - v.wr row)) * v.value_1 row = 0

/-- The active local Mem bridge is a projection of the generated 0-23
segment/continuity surface. -/
theorem core_every_row_of_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row) :
    core_every_row v row := by
  rcases h with
    ⟨_, _, _, h3, h4, h5, h6, h7, h8, _, _, _, _, _, _, _, _, _,
      h18, _, _, h21, _, h23⟩
  exact ⟨h3, h4, h5, h6, h7, h8, h18, h21, h23⟩

/-! ## Generated permutation accumulator surface

The extractor emits constraints 24-33 for the `std_sum` / direct-update
accumulator part of Mem. These formulas are still algebraic row facts; the
semantic proof that they imply public memory-bus chronology and replay
soundness belongs in the Clean/global trace layer.
-/

/-- Non-witness Mem columns used by generated constraints 24-33. -/
structure PermutationColumns (F : Type) [Field F] where
  std_alpha : F
  std_gamma : F
  l1 : ℕ → F
  im_direct_0 : F
  im_direct_1 : F
  im_direct_2 : F
  im_direct_3 : F
  im_direct_4 : F
  im_direct_5 : F

@[simp]
def gsum_increment_1
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.increment_1 row * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def gsum_dual_step
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  ((v.step_dual row - v.step row) - v.wr row) * cols.std_alpha
    + 102 + cols.std_gamma

@[simp]
def gsum_increment_0
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.increment_0 row * cols.std_alpha + 104 + cols.std_gamma

@[simp]
def gsum_primary_mem
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  (((((((v.value_1 row * cols.std_alpha + v.value_0 row) * cols.std_alpha
      + 8) * cols.std_alpha + v.step row) * cols.std_alpha
      + v.addr row * 8) * cols.std_alpha + (v.wr row + 1))
      * cols.std_alpha + 10) + cols.std_gamma)

@[simp]
def gsum_dual_mem
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  (((((((v.value_1 row * cols.std_alpha + v.value_0 row) * cols.std_alpha
      + 8) * cols.std_alpha + v.step_dual row) * cols.std_alpha
      + v.addr row * 8) * cols.std_alpha + 1)
      * cols.std_alpha + 10) + cols.std_gamma)

@[simp]
def direct_gsum_0
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  ((((((seg.previous_segment_value_1 * cols.std_alpha
      + seg.previous_segment_value_0) * cols.std_alpha
      + seg.previous_segment_step) * cols.std_alpha
      + seg.previous_segment_addr) * cols.std_alpha
      + seg.segment_id) * cols.std_alpha + 2684354560)
      * cols.std_alpha + 11) + cols.std_gamma

@[simp]
def direct_gsum_1
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  ((((((seg.segment_last_value_1 * cols.std_alpha
      + seg.segment_last_value_0) * cols.std_alpha
      + seg.segment_last_step) * cols.std_alpha
      + seg.segment_last_addr) * cols.std_alpha
      + (seg.segment_id + 1)) * cols.std_alpha + 2684354560)
      * cols.std_alpha + 11) + cols.std_gamma

@[simp]
def direct_gsum_distance_base_0
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_base_0 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def direct_gsum_distance_base_1
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_base_1 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def direct_gsum_distance_end_0
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_end_0 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def direct_gsum_distance_end_1
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_end_1 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def gsum_accumulator_delta
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.gsum row - v.gsum (row - 1) * (1 - cols.l1 row)
    - (v.im_0 row + v.im_1 row)

/-- Generated Mem constraints 24-33. -/
@[simp]
def permutation_every_row
    (seg : SegmentColumns F) (cols : PermutationColumns F)
    (v : Valid_Mem F F) (row : ℕ) : Prop :=
  v.im_0 row * (gsum_increment_1 cols v row * gsum_dual_step cols v row)
      - ((18446744069414584320 * gsum_dual_step cols v row)
        + ((0 - v.sel_dual row) * gsum_increment_1 cols v row)) = 0
  ∧ v.im_1 row * (gsum_primary_mem cols v row * gsum_dual_mem cols v row)
      - (v.sel row * gsum_dual_mem cols v row
        + v.sel_dual row * gsum_primary_mem cols v row) = 0
  ∧ gsum_accumulator_delta cols v row * gsum_increment_0 cols v row + 1 = 0
  ∧ cols.im_direct_0 * direct_gsum_0 seg cols + 1 = 0
  ∧ cols.im_direct_1 * direct_gsum_1 seg cols
      - (1 - seg.is_last_segment) = 0
  ∧ cols.im_direct_2 * direct_gsum_distance_base_0 seg cols + 1 = 0
  ∧ cols.im_direct_3 * direct_gsum_distance_base_1 seg cols + 1 = 0
  ∧ cols.im_direct_4 * direct_gsum_distance_end_0 seg cols + 1 = 0
  ∧ cols.im_direct_5 * direct_gsum_distance_end_1 seg cols + 1 = 0
  ∧ cols.l1 (row + 1) *
      (seg.segment_id - v.gsum row
        - (((((cols.im_direct_0 + cols.im_direct_1) + cols.im_direct_2)
          + cols.im_direct_3) + cols.im_direct_4) + cols.im_direct_5)) = 0

/-- The complete generated Mem every-row surface currently named in source. -/
@[simp]
def generated_every_row
    (seg : SegmentColumns F) (perm : PermutationColumns F)
    (v : Valid_Mem F F) (row : ℕ) : Prop :=
  segment_every_row seg v row ∧ permutation_every_row seg perm v row

/-- The active local Mem bridge is also a projection of the full generated
every-row surface. -/
theorem core_every_row_of_generated_every_row
    {seg : SegmentColumns F} {perm : PermutationColumns F}
    {v : Valid_Mem F F} {row : ℕ}
    (h : generated_every_row seg perm v row) :
    core_every_row v row :=
  core_every_row_of_segment_every_row h.1

end ZiskFv.Airs.Mem
