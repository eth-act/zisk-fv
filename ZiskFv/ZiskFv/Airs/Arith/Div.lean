import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Arith
import ZiskFv.Airs.OperationBus

/-!
Named-column mirror of the ZisK `Arith` AIR, restricted to the **DIV/REM
subset** (Phase 3C Track T-D). Clone of `Airs/Arith/Mul.lean`, specialized
to the division rows that serve RV64 DIV, DIVU, REM, REMU.

The Arith state machine is the same AIR used for MUL, but a *single row*
serves a pair of opcodes dispatched through the `div` / `main_div` /
`main_mul` selectors:

```
// arith.pil:222-234 — row-type table
// div m32 sa  sb  primary  secondary  opcodes
//  0   0   1   1  mul      mulh       0xb4 180  0xb5 181   (MUL family)
//  1   0   0   0  divu     remu       0xb8 184  0xb9 185
//  1   0   1   1  div      rem        0xba 186  0xbb 187
```

Each "DIV family" Arith row has `div = 1`. The bus-result lane is
selected per opcode:

* **DIV / DIVU (primary, `main_div = 1`, `main_mul = 0`):** bus emits the
  *quotient*, packed into the Arith column `a[0..3]`:
    * `bus_res0 = a[0] + a[1] * 2^16`
    * `bus_res1_64 = a[2] + a[3] * 2^16`
  (arith.pil:253-259 — `main_div * (a[0] + a[1] * CHUNK_SIZE)` summand).
* **REM / REMU (secondary, `main_mul = 0`, `main_div = 0` →
  `secondary = 1`):** bus emits the *remainder*, packed into the Arith
  column `d[0..3]`:
    * `bus_res0 = d[0] + d[1] * 2^16`
    * `bus_res1_64 = d[2] + d[3] * 2^16`
  (arith.pil:253-259 — `secondary * (d[0] + d[1] * CHUNK_SIZE)` summand).

The Arith column `c[]` holds the dividend (input `a`, post-renaming) on
division rows — per `bus_a0 = div * (c[0] + c[1]*CHUNK_SIZE) + (1 - div)
* (a[0] + a[1]*CHUNK_SIZE)` at arith.pil:247: on DIV rows (`div = 1`),
the bus `a` lane comes from `c[]`.

As with `Valid_ArithMul`, the A5 archetype **does not derive** the
division carry-chain correctness (constraints 31–38 interpreted with
`div = 1`) — that's Phase 4 audit work. The compositional proof only
consumes the bus-match identity.

Mirrors `Airs/Arith/Mul.lean` — named columns + `constraint_N_of_extraction`
bridges for the shared booleans. The column indices are the same (the
Arith AIR is a single schema; DIV-family rows just set different
selectors).
-/

namespace ZiskFv.Airs.ArithDiv

open Goldilocks
open Arith.extraction

/-- Named accessors for one row of ZisK's `Arith` AIR, restricted to the
    DIV/REM-relevant columns.

    Column layout from `ZiskFv/ZiskFv/Extraction/Arith.lean`:

    * `a[0..3]`, `b[0..3]`, `c[0..3]`, `d[0..3]` — stage-1 cols 7–22.
      On DIV/DIVU rows (`main_div = 1`, primary) the quotient is packed
      into `a[0..3]`, the remainder into `d[0..3]`. On REM/REMU rows
      (secondary) the same layout holds — every Arith division row
      witnesses both quotient (a) and remainder (d); the Main-side
      opcode selects which pair of lanes goes on the bus.
    * `na`, `nb`, `nr`, `np`, `sext`, `m32`, `div` — stage-1 cols 23–29.
      For 64-bit DIVU/REMU all zero; for signed DIV/REM `na`, `nb`, `np`,
      `nr` follow the operand/quotient/remainder signs. `div = 1` marks
      the row as division (vs. multiplication), `m32 = 0` selects the
      64-bit width (divu_w/div_w/remu_w/rem_w out of scope).
    * `main_mul`, `main_div` — stage-1 cols 33–34. On DIV/DIVU rows
      `main_div = 1`, `main_mul = 0`; on REM/REMU rows (secondary)
      both are zero. The `secondary` row-expr (arith.pil:246) is
      `1 - main_mul - main_div`.
    * `op` — stage-1 col 39 — the 8-bit opcode literal
      (0xb8..0xbb for 64-bit DIV family).
    * `multiplicity` — stage-1 col 41 — operation-bus consume multiplicity.
    * `bus_res1` — stage-1 col 40 — the range-checked high-32 witness
      column. For the 64-bit div cases (sext = 0, m32 = 0) it equals
      `bus_res1_64` (see constraint 46 in `Extraction/Arith`). -/
structure Valid_ArithDiv (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  a_0 : ℕ → F
  a_1 : ℕ → F
  a_2 : ℕ → F
  a_3 : ℕ → F
  b_0 : ℕ → F
  b_1 : ℕ → F
  b_2 : ℕ → F
  b_3 : ℕ → F
  c_0 : ℕ → F
  c_1 : ℕ → F
  c_2 : ℕ → F
  c_3 : ℕ → F
  d_0 : ℕ → F
  d_1 : ℕ → F
  d_2 : ℕ → F
  d_3 : ℕ → F
  na : ℕ → F
  nb : ℕ → F
  nr : ℕ → F
  np : ℕ → F
  sext : ℕ → F
  m32 : ℕ → F
  div : ℕ → F
  main_div : ℕ → F
  main_mul : ℕ → F
  op : ℕ → F
  bus_res1 : ℕ → F
  multiplicity : ℕ → F
  a_0_def : ∀ row,
    a_0 row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  a_1_def : ∀ row,
    a_1 row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  a_2_def : ∀ row,
    a_2 row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  a_3_def : ∀ row,
    a_3 row = Circuit.main circuit (id := 1) (column := 10) (row := row) (rotation := 0)
  b_0_def : ∀ row,
    b_0 row = Circuit.main circuit (id := 1) (column := 11) (row := row) (rotation := 0)
  b_1_def : ∀ row,
    b_1 row = Circuit.main circuit (id := 1) (column := 12) (row := row) (rotation := 0)
  b_2_def : ∀ row,
    b_2 row = Circuit.main circuit (id := 1) (column := 13) (row := row) (rotation := 0)
  b_3_def : ∀ row,
    b_3 row = Circuit.main circuit (id := 1) (column := 14) (row := row) (rotation := 0)
  c_0_def : ∀ row,
    c_0 row = Circuit.main circuit (id := 1) (column := 15) (row := row) (rotation := 0)
  c_1_def : ∀ row,
    c_1 row = Circuit.main circuit (id := 1) (column := 16) (row := row) (rotation := 0)
  c_2_def : ∀ row,
    c_2 row = Circuit.main circuit (id := 1) (column := 17) (row := row) (rotation := 0)
  c_3_def : ∀ row,
    c_3 row = Circuit.main circuit (id := 1) (column := 18) (row := row) (rotation := 0)
  d_0_def : ∀ row,
    d_0 row = Circuit.main circuit (id := 1) (column := 19) (row := row) (rotation := 0)
  d_1_def : ∀ row,
    d_1 row = Circuit.main circuit (id := 1) (column := 20) (row := row) (rotation := 0)
  d_2_def : ∀ row,
    d_2 row = Circuit.main circuit (id := 1) (column := 21) (row := row) (rotation := 0)
  d_3_def : ∀ row,
    d_3 row = Circuit.main circuit (id := 1) (column := 22) (row := row) (rotation := 0)
  na_def : ∀ row,
    na row = Circuit.main circuit (id := 1) (column := 23) (row := row) (rotation := 0)
  nb_def : ∀ row,
    nb row = Circuit.main circuit (id := 1) (column := 24) (row := row) (rotation := 0)
  nr_def : ∀ row,
    nr row = Circuit.main circuit (id := 1) (column := 25) (row := row) (rotation := 0)
  np_def : ∀ row,
    np row = Circuit.main circuit (id := 1) (column := 26) (row := row) (rotation := 0)
  sext_def : ∀ row,
    sext row = Circuit.main circuit (id := 1) (column := 27) (row := row) (rotation := 0)
  m32_def : ∀ row,
    m32 row = Circuit.main circuit (id := 1) (column := 28) (row := row) (rotation := 0)
  div_def : ∀ row,
    div row = Circuit.main circuit (id := 1) (column := 29) (row := row) (rotation := 0)
  main_div_def : ∀ row,
    main_div row = Circuit.main circuit (id := 1) (column := 33) (row := row) (rotation := 0)
  main_mul_def : ∀ row,
    main_mul row = Circuit.main circuit (id := 1) (column := 34) (row := row) (rotation := 0)
  op_def : ∀ row,
    op row = Circuit.main circuit (id := 1) (column := 39) (row := row) (rotation := 0)
  bus_res1_def : ∀ row,
    bus_res1 row = Circuit.main circuit (id := 1) (column := 40) (row := row) (rotation := 0)
  multiplicity_def : ∀ row,
    multiplicity row = Circuit.main circuit (id := 1) (column := 41) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- `main_mul` and `main_div` are mutually exclusive: `main_mul * main_div = 0`.
    Rewrites `constraint_2_every_row`. Same constraint as MUL rows — this
    is a global Arith-AIR boolean not specific to mode. -/
@[simp]
def main_mul_div_disjoint (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.main_mul row * v.main_div row = 0

/-- `m32` is boolean — rewrites `constraint_40_every_row`. -/
@[simp]
def boolean_m32 (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.m32 row * (1 - v.m32 row) = 0

/-- `na` is boolean — rewrites `constraint_41_every_row`. -/
@[simp]
def boolean_na (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.na row * (1 - v.na row) = 0

/-- `nb` is boolean — rewrites `constraint_42_every_row`. -/
@[simp]
def boolean_nb (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.nb row * (1 - v.nb row) = 0

/-- `nr` is boolean — rewrites `constraint_43_every_row`. -/
@[simp]
def boolean_nr (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.nr row * (1 - v.nr row) = 0

/-- `np` is boolean — rewrites `constraint_44_every_row`. -/
@[simp]
def boolean_np (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.np row * (1 - v.np row) = 0

/-- `sext` is boolean — rewrites `constraint_45_every_row`. -/
@[simp]
def boolean_sext (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  v.sext row * (1 - v.sext row) = 0

/-- **DIV/REM-subset mode predicates bundled.** Same boolean-selector
    subset the MUL-family compositional proof relies on — these
    constraints are AIR-global, not mode-specific. The carry-chain
    constraints (31–38), specialized to `div = 1`, remain reachable
    via the raw extraction bridges but are carried through to Phase-4
    audit. -/
@[simp]
def div_mode_booleans (v : Valid_ArithDiv C F ExtF) (row : ℕ) : Prop :=
  main_mul_div_disjoint v row
  ∧ boolean_m32 v row
  ∧ boolean_na v row
  ∧ boolean_nb v row
  ∧ boolean_nr v row
  ∧ boolean_np v row
  ∧ boolean_sext v row

section extraction_bridge

@[simp]
lemma constraint_2_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_2_every_row v.circuit row ↔ main_mul_div_disjoint v row := by
  unfold constraint_2_every_row main_mul_div_disjoint
  rw [v.main_mul_def, v.main_div_def]

@[simp]
lemma constraint_40_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_40_every_row v.circuit row ↔ boolean_m32 v row := by
  unfold constraint_40_every_row boolean_m32
  rw [v.m32_def]

@[simp]
lemma constraint_41_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_41_every_row v.circuit row ↔ boolean_na v row := by
  unfold constraint_41_every_row boolean_na
  rw [v.na_def]

@[simp]
lemma constraint_42_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_42_every_row v.circuit row ↔ boolean_nb v row := by
  unfold constraint_42_every_row boolean_nb
  rw [v.nb_def]

@[simp]
lemma constraint_43_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_43_every_row v.circuit row ↔ boolean_nr v row := by
  unfold constraint_43_every_row boolean_nr
  rw [v.nr_def]

@[simp]
lemma constraint_44_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_44_every_row v.circuit row ↔ boolean_np v row := by
  unfold constraint_44_every_row boolean_np
  rw [v.np_def]

@[simp]
lemma constraint_45_of_extraction
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) :
    constraint_45_every_row v.circuit row ↔ boolean_sext v row := by
  unfold constraint_45_every_row boolean_sext
  rw [v.sext_def]

end extraction_bridge

section BusEmission

open ZiskFv.Airs.OperationBus

/-- Arith's operation-bus emission for a DIV-family row, selected by
    primary (`main_div = 1`) vs. secondary (`secondary = 1`) mode.

    Mirrors the `proves_operation(op:, a:, b:, c:, flag:, mul:)` call at
    `vendor/zisk/state-machines/arith/pil/arith.pil:269-270`. The bus
    `a` / `b` / `c` lanes project through:

    * `bus_a0` = `div * (c[0] + c[1] * 2^16) + (1 - div) * (a[0] + a[1] * 2^16)`
      (arith.pil:247); on DIV rows (`div = 1`) this is `c[0] + c[1] * 2^16`.
    * `bus_a1` = `div * (c[2] + c[3] * 2^16) + (1 - div) * (a[2] + a[3] * 2^16)`
      (arith.pil:248); on DIV rows `c[2] + c[3] * 2^16`.
    * `bus_b0` / `bus_b1` = `b[0] + b[1]*2^16` / `b[2] + b[3]*2^16`
      (arith.pil:250-251); same as MUL.
    * `bus_res0` = `secondary * (d[0] + d[1]*2^16) + main_mul * (c[0] + c[1]*2^16)
                  + main_div * (a[0] + a[1]*2^16)` (arith.pil:253-255).
      For primary DIV/DIVU (`main_div = 1`) this is `a[0] + a[1]*2^16`
      (the quotient low lane); for secondary REM/REMU (both mains 0,
      `secondary = 1`) this is `d[0] + d[1]*2^16` (the remainder low lane).
    * `bus_res1_64` similarly (arith.pil:257-259) selects `a[2] + a[3]*2^16`
      for DIV/DIVU and `d[2] + d[3]*2^16` for REM/REMU; `bus_res1` is the
      range-checked 32-bit witness column pinned via constraint 46 on the
      64-bit case (sext = 0, m32 = 0) to `bus_res1_64`.

    Since the bus-result projection is selector-dependent, we
    parameterize this over two separate builders — one for primary
    DIV/DIVU (quotient = `a[]`), one for secondary REM/REMU
    (remainder = `d[]`). The bus-row Lean structure is the same
    `OperationBusEntry`; only which Arith columns flow into `c_lo` /
    `c_hi` differs.

    On DIV rows we also have `flag = div_by_zero`; for our compositional
    archetype this sits as a free field on the bus entry (it's a Phase-4
    concern — we leave `flag = 0` here, matching the semantics that a
    non-div-by-zero divide emits `flag = 0` and the Sail side never
    observes the flag directly; div-by-zero is handled by the PIL +
    arith_table assumption network). -/
@[simp]
def opBus_row_ArithDiv {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.multiplicity row
    op := v.op row
    -- DIV rows: `div = 1` → bus `a` comes from `c[]`.
    a_lo := v.c_0 row + v.c_1 row * 65536
    a_hi := v.c_2 row + v.c_3 row * 65536
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
    -- Quotient output lane: `a[0] + a[1] * 2^16` on main_div = 1.
    c_lo := v.a_0 row + v.a_1 row * 65536
    c_hi := v.bus_res1 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Arith's operation-bus emission for a DIV-family row in **secondary**
    mode (REM / REMU). On secondary rows `main_mul = 0`, `main_div = 0`,
    so `secondary = 1` and the bus `c` lane comes from `d[]` — the
    remainder output.

    Same row-level layout as `opBus_row_ArithDiv` except the result lane
    is packed from `d[0..3]` rather than `a[0..3]`. -/
@[simp]
def opBus_row_ArithDivSecondary {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (v : Valid_ArithDiv C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := v.multiplicity row
    op := v.op row
    -- DIV rows: `div = 1` → bus `a` comes from `c[]`.
    a_lo := v.c_0 row + v.c_1 row * 65536
    a_hi := v.c_2 row + v.c_3 row * 65536
    b_lo := v.b_0 row + v.b_1 row * 65536
    b_hi := v.b_2 row + v.b_3 row * 65536
    -- Remainder output lane: `d[0] + d[1] * 2^16` on secondary = 1.
    c_lo := v.d_0 row + v.d_1 row * 65536
    c_hi := v.bus_res1 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

end BusEmission

end ZiskFv.Airs.ArithDiv
