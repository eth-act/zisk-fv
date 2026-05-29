import Mathlib

import ZiskFv.Field.Goldilocks

/-!
Named-column mirror of the ZisK `Mem` AIR (pilout idx 2).

After the OpenVM Circuit retirement (Phase D), `Valid_Mem` is a plain
named-column record; the canonical AIR view is the Clean
`Air.Flat.Component` at `ZiskFv/AirsClean/Mem/`.

Only the nine F-typed constraints (3, 4, 5, 6, 7, 8, 18, 21, 23) are
named here; the rest mix `F` (witness cells) with `ExtF` (challenges /
airvalues / permutation accumulators) and are handled compositionally
via the memory-bus / continuation models (`Airs/MemoryBus.lean` and
friends).

The F-typed surface bridged here covers the per-row local invariants
of the `Mem` AIR's primary witness columns: booleanity of `sel`,
`sel_dual`, `addr_changes`, `wr`; the `wr ⇒ sel` and `sel_dual ⇒ sel`
implications (encoded as products); the `read_same_addr` definitional
identity; and the "address change without write zeros the value"
constraints. Continuity (cross-row) constraints involve airvalues and
appear in the stub bucket.

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

/-- The nine F-typed every-row constraints bundled. The remaining 25
    extraction constraints (mixed F/ExtF) are the permutation /
    direct-update / continuity stubs and are handled compositionally
    against the memory-bus model in `Airs/MemoryBus.lean`. -/
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

end ZiskFv.Airs.Mem
