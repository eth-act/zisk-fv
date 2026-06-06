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

/-- At a non-boundary row, the segment previous-address expression is the
    previous row's address. Segment-boundary carry-in is handled separately by
    the global Mem trace construction. -/
theorem segment_previous_addr_eq_previous_of_not_boundary
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h_not_boundary : cols.segment_l1 row = 0) :
    segment_previous_addr cols v row = v.addr (row - 1) := by
  simp [segment_previous_addr, h_not_boundary]

/-- At a non-boundary row, the segment previous-value expression for the low
    chunk is the previous row's low value chunk. -/
theorem segment_previous_value_0_eq_previous_of_not_boundary
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h_not_boundary : cols.segment_l1 row = 0) :
    segment_previous_value_0 cols v row = v.value_0 (row - 1) := by
  simp [segment_previous_value_0, h_not_boundary]

/-- At a non-boundary row, the segment previous-value expression for the high
    chunk is the previous row's high value chunk. -/
theorem segment_previous_value_1_eq_previous_of_not_boundary
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h_not_boundary : cols.segment_l1 row = 0) :
    segment_previous_value_1 cols v row = v.value_1 (row - 1) := by
  simp [segment_previous_value_1, h_not_boundary]

/-- The generated segment constraints imply same-address rows carry the
    previous address at non-boundary positions. -/
theorem addr_eq_previous_of_same_addr_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_same_addr : v.addr_changes row = 0)
    (h_not_boundary : cols.segment_l1 row = 0) :
    v.addr row = v.addr (row - 1) := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h_addr, _, _, _, _⟩
  rw [h_same_addr] at h_addr
  have h_prev :=
    segment_previous_addr_eq_previous_of_not_boundary
      (cols := cols) (v := v) (row := row) h_not_boundary
  rw [h_prev] at h_addr
  linear_combination h_addr

/-- The generated segment constraints imply same-address reads carry the
    previous low value chunk at non-boundary positions. -/
theorem value_0_eq_previous_of_read_same_addr_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_read_same_addr : v.read_same_addr row = 1)
    (h_not_boundary : cols.segment_l1 row = 0) :
    v.value_0 row = v.value_0 (row - 1) := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h_value_0, _, _, _⟩
  rw [h_read_same_addr] at h_value_0
  have h_prev :=
    segment_previous_value_0_eq_previous_of_not_boundary
      (cols := cols) (v := v) (row := row) h_not_boundary
  rw [h_prev] at h_value_0
  linear_combination h_value_0

/-- The generated segment constraints imply same-address reads carry the
    previous high value chunk at non-boundary positions. -/
theorem value_1_eq_previous_of_read_same_addr_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_read_same_addr : v.read_same_addr row = 1)
    (h_not_boundary : cols.segment_l1 row = 0) :
    v.value_1 row = v.value_1 (row - 1) := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h_value_1, _⟩
  rw [h_read_same_addr] at h_value_1
  have h_prev :=
    segment_previous_value_1_eq_previous_of_not_boundary
      (cols := cols) (v := v) (row := row) h_not_boundary
  rw [h_prev] at h_value_1
  linear_combination h_value_1

/-- At a segment-boundary row, the segment previous-address expression is the
    previous segment's carried-out address. -/
theorem segment_previous_addr_eq_previous_segment_of_boundary
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h_boundary : cols.segment_l1 row = 1) :
    segment_previous_addr cols v row = cols.previous_segment_addr := by
  simp [segment_previous_addr, h_boundary]

/-- At a segment-boundary row, the segment previous-value expression for the
    low chunk is the previous segment's carried-out low value chunk. -/
theorem segment_previous_value_0_eq_previous_segment_of_boundary
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h_boundary : cols.segment_l1 row = 1) :
    segment_previous_value_0 cols v row = cols.previous_segment_value_0 := by
  simp [segment_previous_value_0, h_boundary]

/-- At a segment-boundary row, the segment previous-value expression for the
    high chunk is the previous segment's carried-out high value chunk. -/
theorem segment_previous_value_1_eq_previous_segment_of_boundary
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h_boundary : cols.segment_l1 row = 1) :
    segment_previous_value_1 cols v row = cols.previous_segment_value_1 := by
  simp [segment_previous_value_1, h_boundary]

/-- The generated segment constraints record the current low value chunk as
    the segment's carried-out low value when the next row starts a segment. -/
theorem segment_last_value_0_eq_of_next_boundary_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_next_boundary : cols.segment_l1 (row + 1) = 1) :
    v.value_0 row = cols.segment_last_value_0 := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, h_value_0, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _⟩
  rw [h_next_boundary] at h_value_0
  linear_combination h_value_0

/-- The generated segment constraints record the current high value chunk as
    the segment's carried-out high value when the next row starts a segment. -/
theorem segment_last_value_1_eq_of_next_boundary_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_next_boundary : cols.segment_l1 (row + 1) = 1) :
    v.value_1 row = cols.segment_last_value_1 := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, h_value_1, _, _, _, _, _, _, _, _,
      _, _, _, _, _⟩
  rw [h_next_boundary] at h_value_1
  linear_combination h_value_1

/-- The generated segment constraints record the current address as the
    segment's carried-out address when the next row starts a segment. -/
theorem segment_last_addr_eq_of_next_boundary_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_next_boundary : cols.segment_l1 (row + 1) = 1) :
    v.addr row = cols.segment_last_addr := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, h_addr, _, _, _, _, _, _, _,
      _, _, _, _, _⟩
  rw [h_next_boundary] at h_addr
  linear_combination h_addr

/-- The generated segment constraints record the current effective step as the
    segment's carried-out step when the next row starts a segment. -/
theorem segment_last_step_eq_of_next_boundary_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_next_boundary : cols.segment_l1 (row + 1) = 1) :
    v.sel_dual row * (v.step_dual row - v.step row) + v.step row =
      cols.segment_last_step := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_step, _, _, _, _, _, _,
      _, _, _, _, _⟩
  rw [h_next_boundary] at h_step
  linear_combination h_step

/-- At a non-boundary row, the generated previous-step witness is the
    previous row's effective step. -/
theorem previous_step_eq_previous_row_step_of_not_boundary_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_not_boundary : cols.segment_l1 row = 0) :
    v.previous_step row = previous_row_step v row := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_previous_step,
      _, _, _, _, _, _, _, _⟩
  rw [h_not_boundary] at h_previous_step
  linear_combination h_previous_step

/-- At a segment-boundary row, the generated previous-step witness is the
    previous segment's carried-out effective step. -/
theorem previous_step_eq_previous_segment_step_of_boundary_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_boundary : cols.segment_l1 row = 1) :
    v.previous_step row = cols.previous_segment_step := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_previous_step,
      _, _, _, _, _, _, _, _⟩
  rw [h_boundary] at h_previous_step
  linear_combination h_previous_step

/-- On same-address rows, the generated increment equation reduces to the
    chronological step delta. -/
theorem delta_step_eq_increment_of_same_addr_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_same_addr : v.addr_changes row = 0) :
    delta_step v row =
      v.increment_0 row + 4194304 * v.increment_1 row + 1 := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_increment,
      _, _, _, _, _, _, _⟩
  rw [h_same_addr] at h_increment
  linear_combination -h_increment

/-- On address-change rows, the generated increment equation reduces to the
    address delta. -/
theorem delta_addr_eq_increment_of_addr_change_segment_every_row
    {cols : SegmentColumns F} {v : Valid_Mem F F} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_addr_change : v.addr_changes row = 1) :
    delta_addr cols v row =
      v.increment_0 row + 4194304 * v.increment_1 row + 1 := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_increment,
      _, _, _, _, _, _, _⟩
  rw [h_addr_change] at h_increment
  linear_combination -h_increment

/-- Nat interpretation of the PIL `l_increment`/`h_increment` pair.
    In `mem.pil`, `l_increment` is `bits(22)` and `h_increment` is
    `bits(16)`, and the field expression is
    `l_increment + 2^22 * h_increment + 1`. -/
@[simp]
def incrementNat (v : Valid_Mem FGL FGL) (row : ℕ) : ℕ :=
  (v.increment_0 row).val + 4194304 * (v.increment_1 row).val + 1

/-- PIL range facts for the mutable-Mem increment chunks. These are the
    `range_check` obligations at `mem.pil:384-385`. -/
def increment_chunks_in_range (v : Valid_Mem FGL FGL) (row : ℕ) : Prop :=
  (v.increment_0 row).val < 2 ^ 22 ∧ (v.increment_1 row).val < 2 ^ 16

/-- The increment expression is strictly positive as a Nat. -/
theorem incrementNat_pos (v : Valid_Mem FGL FGL) (row : ℕ) :
    0 < incrementNat v row := by
  simp [incrementNat]

/-- The range-checked increment expression is at most `2^38`. The upper
    bound can be attained because the PIL expression adds one after packing
    the two chunks. -/
theorem incrementNat_le_two_pow_38
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_range : increment_chunks_in_range v row) :
    incrementNat v row ≤ 2 ^ 38 := by
  rcases h_range with ⟨h_lo, h_hi⟩
  simp [incrementNat] at *
  omega

/-- The range-checked increment expression is far below the Goldilocks
    modulus, so later field/Nat bridges can use it as a no-wrap witness. -/
theorem incrementNat_lt_goldilocks_modulus
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_range : increment_chunks_in_range v row) :
    incrementNat v row < 18446744069414584321 := by
  have h_le := incrementNat_le_two_pow_38 (v := v) (row := row) h_range
  norm_num at h_le ⊢
  omega

/-- The field expression in the generated increment constraint is the field
    cast of the Nat interpretation. -/
theorem incrementNat_cast_eq_field_increment
    (v : Valid_Mem FGL FGL) (row : ℕ) :
    ((incrementNat v row : ℕ) : FGL) =
      v.increment_0 row + 4194304 * v.increment_1 row + 1 := by
  simp [incrementNat]

/-- Under the PIL chunk range checks, the field increment expression has the
    Nat representative `incrementNat`. This is the no-wrap bridge needed by
    chronology proofs that move from generated field equalities to Nat order. -/
theorem field_increment_val_eq_incrementNat
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_range : increment_chunks_in_range v row) :
    (v.increment_0 row + 4194304 * v.increment_1 row + 1 : FGL).val =
      incrementNat v row := by
  have h_cast := incrementNat_cast_eq_field_increment v row
  have h_lt := incrementNat_lt_goldilocks_modulus (v := v) (row := row) h_range
  calc
    (v.increment_0 row + 4194304 * v.increment_1 row + 1 : FGL).val =
        (((incrementNat v row : ℕ) : FGL)).val := by
      rw [h_cast.symm]
    _ = incrementNat v row := by
      exact Nat.mod_eq_of_lt h_lt

/-- Same-address generated segment constraints give the exact Nat
    representative of the chronological step delta. -/
theorem delta_step_val_eq_incrementNat_of_same_addr_segment_every_row
    {cols : SegmentColumns FGL} {v : Valid_Mem FGL FGL} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_same_addr : v.addr_changes row = 0)
    (h_range : increment_chunks_in_range v row) :
    (delta_step v row).val = incrementNat v row := by
  have h_delta :=
    delta_step_eq_increment_of_same_addr_segment_every_row
      (cols := cols) (v := v) (row := row) h h_same_addr
  calc
    (delta_step v row).val =
        (v.increment_0 row + 4194304 * v.increment_1 row + 1 : FGL).val := by
      rw [h_delta]
    _ = incrementNat v row :=
      field_increment_val_eq_incrementNat (v := v) (row := row) h_range

/-- Same-address generated segment constraints make the chronological step
    delta strictly positive at the Nat-representative level. -/
theorem delta_step_val_pos_of_same_addr_segment_every_row
    {cols : SegmentColumns FGL} {v : Valid_Mem FGL FGL} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_same_addr : v.addr_changes row = 0)
    (h_range : increment_chunks_in_range v row) :
    0 < (delta_step v row).val := by
  rw [delta_step_val_eq_incrementNat_of_same_addr_segment_every_row
    (cols := cols) (v := v) (row := row) h h_same_addr h_range]
  exact incrementNat_pos v row

/-- Address-change generated segment constraints give the exact Nat
    representative of the chronological address delta. -/
theorem delta_addr_val_eq_incrementNat_of_addr_change_segment_every_row
    {cols : SegmentColumns FGL} {v : Valid_Mem FGL FGL} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_addr_change : v.addr_changes row = 1)
    (h_range : increment_chunks_in_range v row) :
    (delta_addr cols v row).val = incrementNat v row := by
  have h_delta :=
    delta_addr_eq_increment_of_addr_change_segment_every_row
      (cols := cols) (v := v) (row := row) h h_addr_change
  calc
    (delta_addr cols v row).val =
        (v.increment_0 row + 4194304 * v.increment_1 row + 1 : FGL).val := by
      rw [h_delta]
    _ = incrementNat v row :=
      field_increment_val_eq_incrementNat (v := v) (row := row) h_range

/-- Address-change generated segment constraints make the chronological address
    delta strictly positive at the Nat-representative level. -/
theorem delta_addr_val_pos_of_addr_change_segment_every_row
    {cols : SegmentColumns FGL} {v : Valid_Mem FGL FGL} {row : ℕ}
    (h : segment_every_row cols v row)
    (h_addr_change : v.addr_changes row = 1)
    (h_range : increment_chunks_in_range v row) :
    0 < (delta_addr cols v row).val := by
  rw [delta_addr_val_eq_incrementNat_of_addr_change_segment_every_row
    (cols := cols) (v := v) (row := row) h h_addr_change h_range]
  exact incrementNat_pos v row

/-- PIL bit-range facts for the mutable-Mem step columns. In `mem.pil`,
    `step`, `step_dual`, and `previous_step` are `bits(MEM_STEP_BITS)`, and
    the pinned RV64IM configuration has `MEM_STEP_BITS = 40`. -/
def step_columns_in_range (v : Valid_Mem FGL FGL) (row : ℕ) : Prop :=
  (v.step row).val < 2 ^ 40
    ∧ (v.step_dual row).val < 2 ^ 40
    ∧ (v.previous_step row).val < 2 ^ 40

/-- PIL range-check fact for the dual mutable-Mem step delta:
    `range_check(step_dual - step - wr, 0, 2^24 - 1, sel_dual)`. -/
def dual_step_delta_in_range (v : Valid_Mem FGL FGL) (row : ℕ) : Prop :=
  (v.step_dual row - v.step row - v.wr row : FGL).val < 2 ^ 24

/-- A small Goldilocks no-wrap fact for the dual-step range check. If
    `step_dual - step - wr` has a small representative while the step columns
    are 40-bit and `wr` is one bit, then the field subtraction did not wrap. -/
theorem step_dual_ge_step_add_wr_of_dual_step_delta_range
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_steps : step_columns_in_range v row)
    (h_wr : (v.wr row).val < 2)
    (h_delta : dual_step_delta_in_range v row) :
    (v.step row).val + (v.wr row).val ≤ (v.step_dual row).val := by
  rcases h_steps with ⟨h_step, h_step_dual, _h_previous_step⟩
  have hmod :
      (v.step_dual row - v.step row - v.wr row : FGL).val =
        (18446744069414584321 - (v.wr row).val
          + (18446744069414584321 - (v.step row).val
            + (v.step_dual row).val)) % 18446744069414584321 := by
    simp [Fin.val_sub]
  by_contra hle
  have hlt : (v.step_dual row).val < (v.step row).val + (v.wr row).val := by
    omega
  have hcalc :
      (18446744069414584321 - (v.wr row).val
          + (18446744069414584321 - (v.step row).val
            + (v.step_dual row).val)) % 18446744069414584321 =
        18446744069414584321 -
          ((v.step row).val + (v.wr row).val - (v.step_dual row).val) := by
    have hsmall :
        (v.step row).val + (v.wr row).val - (v.step_dual row).val <
          18446744069414584321 := by
      omega
    have hsum :
        18446744069414584321 - (v.wr row).val
            + (18446744069414584321 - (v.step row).val
              + (v.step_dual row).val) =
          2 * 18446744069414584321 -
            ((v.step row).val + (v.wr row).val - (v.step_dual row).val) := by
      omega
    rw [hsum]
    have hsplit :
        2 * 18446744069414584321 -
            ((v.step row).val + (v.wr row).val - (v.step_dual row).val) =
          18446744069414584321 +
            (18446744069414584321 -
              ((v.step row).val + (v.wr row).val - (v.step_dual row).val)) := by
      omega
    rw [hsplit]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [dual_step_delta_in_range, hmod, hcalc] at h_delta
  omega

/-- Under the dual-step range check, the field expression's representative is
    the ordinary Nat subtraction `step_dual - step - wr`. -/
theorem dual_step_delta_val_eq_nat_sub_of_range
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_steps : step_columns_in_range v row)
    (h_wr : (v.wr row).val < 2)
    (h_delta : dual_step_delta_in_range v row) :
    (v.step_dual row - v.step row - v.wr row : FGL).val =
      (v.step_dual row).val - (v.step row).val - (v.wr row).val := by
  have h_ge :=
    step_dual_ge_step_add_wr_of_dual_step_delta_range
      (v := v) (row := row) h_steps h_wr h_delta
  have hmod :
      (v.step_dual row - v.step row - v.wr row : FGL).val =
        (18446744069414584321 - (v.wr row).val
          + (18446744069414584321 - (v.step row).val
            + (v.step_dual row).val)) % 18446744069414584321 := by
    simp [Fin.val_sub]
  rw [hmod]
  have hsum :
      18446744069414584321 - (v.wr row).val
          + (18446744069414584321 - (v.step row).val
            + (v.step_dual row).val) =
        2 * 18446744069414584321 +
          ((v.step_dual row).val - (v.step row).val - (v.wr row).val) := by
    omega
  rw [hsum]
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by
    rcases h_steps with ⟨h_step, h_step_dual, _h_previous_step⟩
    omega)

/-- The dual-step range check gives timestamp monotonicity inside a dual Mem
    row. -/
theorem step_le_step_dual_of_dual_step_delta_range
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_steps : step_columns_in_range v row)
    (h_wr : (v.wr row).val < 2)
    (h_delta : dual_step_delta_in_range v row) :
    (v.step row).val ≤ (v.step_dual row).val := by
  have h_ge :=
    step_dual_ge_step_add_wr_of_dual_step_delta_range
      (v := v) (row := row) h_steps h_wr h_delta
  omega

/-- If the primary operation is a write (`wr = 1`), the dual Mem timestamp is
    strictly later than the primary timestamp. -/
theorem step_lt_step_dual_of_wr_one_dual_step_delta_range
    {v : Valid_Mem FGL FGL} {row : ℕ}
    (h_steps : step_columns_in_range v row)
    (h_delta : dual_step_delta_in_range v row)
    (h_wr_one : v.wr row = 1) :
    (v.step row).val < (v.step_dual row).val := by
  have h_wr_val : (v.wr row).val = 1 := by
    rw [h_wr_one]
    rfl
  have h_ge :=
    step_dual_ge_step_add_wr_of_dual_step_delta_range
      (v := v) (row := row) h_steps (by omega) h_delta
  omega

/-- Nat interpretation of the two 16-bit distance chunks used for large Mem
    segment-boundary checks. -/
@[simp]
def distanceChunksNat (lo hi : FGL) : ℕ :=
  lo.val + 65536 * hi.val

/-- PIL range facts for a two-chunk large-memory segment distance. -/
def distance_chunks_in_range (lo hi : FGL) : Prop :=
  lo.val < 2 ^ 16 ∧ hi.val < 2 ^ 16

/-- Two 16-bit distance chunks pack to at most `2^32 - 1`. -/
theorem distanceChunksNat_le_two_pow_32_sub_one
    {lo hi : FGL}
    (h_range : distance_chunks_in_range lo hi) :
    distanceChunksNat lo hi ≤ 2 ^ 32 - 1 := by
  rcases h_range with ⟨h_lo, h_hi⟩
  simp [distanceChunksNat] at *
  omega

/-- Packed two-chunk large-memory segment distances are below the Goldilocks
    modulus. -/
theorem distanceChunksNat_lt_goldilocks_modulus
    {lo hi : FGL}
    (h_range : distance_chunks_in_range lo hi) :
    distanceChunksNat lo hi < 18446744069414584321 := by
  have h_le :=
    distanceChunksNat_le_two_pow_32_sub_one (lo := lo) (hi := hi) h_range
  norm_num at h_le ⊢
  omega

/-- The field expression used for large-memory distance chunks is the field
    cast of the Nat interpretation. -/
theorem distanceChunksNat_cast_eq_field_distance (lo hi : FGL) :
    ((distanceChunksNat lo hi : ℕ) : FGL) = lo + 65536 * hi := by
  simp [distanceChunksNat]

/-- Under the PIL chunk range checks, the packed distance field expression
    has the Nat representative `distanceChunksNat`. -/
theorem field_distance_val_eq_distanceChunksNat
    {lo hi : FGL}
    (h_range : distance_chunks_in_range lo hi) :
    (lo + 65536 * hi : FGL).val = distanceChunksNat lo hi := by
  have h_cast := distanceChunksNat_cast_eq_field_distance lo hi
  have h_lt :=
    distanceChunksNat_lt_goldilocks_modulus (lo := lo) (hi := hi) h_range
  calc
    (lo + 65536 * hi : FGL).val =
        (((distanceChunksNat lo hi : ℕ) : FGL)).val := by
      rw [h_cast.symm]
    _ = distanceChunksNat lo hi := by
      exact Nat.mod_eq_of_lt h_lt

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
