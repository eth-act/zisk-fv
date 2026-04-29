import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Mem

/-!
Named-column mirror of the extracted ZisK `Mem` AIR (pilout idx 2),
plus `constraint_N_of_extraction` iff-lemmas bridging each named
predicate back to `Mem.extraction.constraint_N_every_row`.

Mirrors `Airs/Binary/BinaryAdd.lean`. Only the nine F-typed constraints
(3, 4, 5, 6, 7, 8, 18, 21, 23) are bridged here; constraints 0–2,
9–17, 19, 20, 22, 24–33 are skipped at the extraction layer because
they mix `F` (witness cells) with `ExtF` (challenges / airvalues /
permutation accumulators) and are handled compositionally via the
memory-bus / continuation models (`Airs/MemoryBus.lean` and friends).

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
* 10: `increment[0]`
* 11: `increment[1]`
* 12: `read_same_addr`
Stage-2 columns:
* 0: `gsum`
* 1: `im[0]`
* 2: `im[1]`
-/

namespace ZiskFv.Airs.Mem

open Goldilocks
open Mem.extraction

/-- Named accessors for one row of ZisK's `Mem` AIR. -/
structure Valid_Mem (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
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
  /-- Agreement with the extraction layer: each named field refers back to
      the same cell the raw `Circuit.main` accessor would. -/
  addr_def : ∀ row,
    addr row = Circuit.main circuit (id := 1) (column := 0) (row := row) (rotation := 0)
  step_def : ∀ row,
    step row = Circuit.main circuit (id := 1) (column := 1) (row := row) (rotation := 0)
  sel_def : ∀ row,
    sel row = Circuit.main circuit (id := 1) (column := 2) (row := row) (rotation := 0)
  addr_changes_def : ∀ row,
    addr_changes row = Circuit.main circuit (id := 1) (column := 3) (row := row) (rotation := 0)
  step_dual_def : ∀ row,
    step_dual row = Circuit.main circuit (id := 1) (column := 4) (row := row) (rotation := 0)
  sel_dual_def : ∀ row,
    sel_dual row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  value_0_def : ∀ row,
    value_0 row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  value_1_def : ∀ row,
    value_1 row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  wr_def : ∀ row,
    wr row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  previous_step_def : ∀ row,
    previous_step row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  increment_0_def : ∀ row,
    increment_0 row = Circuit.main circuit (id := 1) (column := 10) (row := row) (rotation := 0)
  increment_1_def : ∀ row,
    increment_1 row = Circuit.main circuit (id := 1) (column := 11) (row := row) (rotation := 0)
  read_same_addr_def : ∀ row,
    read_same_addr row = Circuit.main circuit (id := 1) (column := 12) (row := row) (rotation := 0)
  gsum_def : ∀ row,
    gsum row = Circuit.main circuit (id := 2) (column := 0) (row := row) (rotation := 0)
  im_0_def : ∀ row,
    im_0 row = Circuit.main circuit (id := 2) (column := 1) (row := row) (rotation := 0)
  im_1_def : ∀ row,
    im_1 row = Circuit.main circuit (id := 2) (column := 2) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- `sel_dual` is boolean — rewrites `constraint_3_every_row`. -/
@[simp]
def boolean_sel_dual (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  v.sel_dual row * (1 - v.sel_dual row) = 0

/-- `sel_dual` requires `sel` — rewrites `constraint_4_every_row`.
    Encoded multiplicatively as `(1 - sel) * sel_dual = 0`. -/
@[simp]
def sel_dual_implies_sel (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  (1 - v.sel row) * v.sel_dual row = 0

/-- `sel` is boolean — rewrites `constraint_5_every_row`. -/
@[simp]
def boolean_sel (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  v.sel row * (1 - v.sel row) = 0

/-- `addr_changes` is boolean — rewrites `constraint_6_every_row`. -/
@[simp]
def boolean_addr_changes (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  v.addr_changes row * (1 - v.addr_changes row) = 0

/-- `wr` is boolean — rewrites `constraint_7_every_row`. -/
@[simp]
def boolean_wr (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  v.wr row * (1 - v.wr row) = 0

/-- All writes must be sent to the bus — rewrites `constraint_8_every_row`.
    Encoded as `wr * (1 - sel) = 0`. -/
@[simp]
def wr_implies_sel (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  v.wr row * (1 - v.sel row) = 0

/-- Definitional identity for `read_same_addr` —
    rewrites `constraint_18_every_row`. -/
@[simp]
def read_same_addr_def_eq (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  v.read_same_addr row - (1 - v.addr_changes row) * (1 - v.wr row) = 0

/-- Address change without write zeros the low value chunk —
    rewrites `constraint_21_every_row`. -/
@[simp]
def addr_change_no_write_zeros_value_0 (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  (v.addr_changes row * (1 - v.wr row)) * v.value_0 row = 0

/-- Address change without write zeros the high value chunk —
    rewrites `constraint_23_every_row`. -/
@[simp]
def addr_change_no_write_zeros_value_1 (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  (v.addr_changes row * (1 - v.wr row)) * v.value_1 row = 0

/-- The nine F-typed every-row constraints bundled. The remaining 25
    extraction constraints (mixed F/ExtF) are the permutation /
    direct-update / continuity stubs and are handled compositionally
    against the memory-bus model in `Airs/MemoryBus.lean`. -/
@[simp]
def core_every_row (v : Valid_Mem C F ExtF) (row : ℕ) : Prop :=
  boolean_sel_dual v row
  ∧ sel_dual_implies_sel v row
  ∧ boolean_sel v row
  ∧ boolean_addr_changes v row
  ∧ boolean_wr v row
  ∧ wr_implies_sel v row
  ∧ read_same_addr_def_eq v row
  ∧ addr_change_no_write_zeros_value_0 v row
  ∧ addr_change_no_write_zeros_value_1 v row

section extraction_bridge

/-- Named `boolean_sel_dual` is logically equivalent to the raw
    `constraint_3_every_row`. -/
@[simp]
lemma constraint_3_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_3_every_row v.circuit row ↔ boolean_sel_dual v row := by
  unfold constraint_3_every_row boolean_sel_dual
  rw [v.sel_dual_def]

@[simp]
lemma constraint_4_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_4_every_row v.circuit row ↔ sel_dual_implies_sel v row := by
  unfold constraint_4_every_row sel_dual_implies_sel
  rw [v.sel_def, v.sel_dual_def]

@[simp]
lemma constraint_5_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_5_every_row v.circuit row ↔ boolean_sel v row := by
  unfold constraint_5_every_row boolean_sel
  rw [v.sel_def]

@[simp]
lemma constraint_6_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_6_every_row v.circuit row ↔ boolean_addr_changes v row := by
  unfold constraint_6_every_row boolean_addr_changes
  rw [v.addr_changes_def]

@[simp]
lemma constraint_7_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_7_every_row v.circuit row ↔ boolean_wr v row := by
  unfold constraint_7_every_row boolean_wr
  rw [v.wr_def]

@[simp]
lemma constraint_8_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_8_every_row v.circuit row ↔ wr_implies_sel v row := by
  unfold constraint_8_every_row wr_implies_sel
  rw [v.sel_def, v.wr_def]

@[simp]
lemma constraint_18_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_18_every_row v.circuit row ↔ read_same_addr_def_eq v row := by
  unfold constraint_18_every_row read_same_addr_def_eq
  rw [v.addr_changes_def, v.wr_def, v.read_same_addr_def]

@[simp]
lemma constraint_21_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_21_every_row v.circuit row ↔ addr_change_no_write_zeros_value_0 v row := by
  unfold constraint_21_every_row addr_change_no_write_zeros_value_0
  rw [v.addr_changes_def, v.wr_def, v.value_0_def]

@[simp]
lemma constraint_23_of_extraction
    (v : Valid_Mem C F ExtF) (row : ℕ) :
    constraint_23_every_row v.circuit row ↔ addr_change_no_write_zeros_value_1 v row := by
  unfold constraint_23_every_row addr_change_no_write_zeros_value_1
  rw [v.addr_changes_def, v.wr_def, v.value_1_def]

end extraction_bridge

end ZiskFv.Airs.Mem
