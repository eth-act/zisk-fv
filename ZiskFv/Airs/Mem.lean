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

end ZiskFv.Airs.Mem
