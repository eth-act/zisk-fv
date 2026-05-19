import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Main.Main

/-!
# MemoryBus.Projection — register-bus 6-slot entry shape and Main row projections

The PIL-level memory bus (`bus_id = 10`) emits register-side entries as
6-tuples `[as, ptr, mem_step, bytes, value_lo, value_hi]`, where the
value carried is a 64-bit register split into two 32-bit lanes (PIL
source: `state-machines/main/pil/main.pil:300-328`,
`zisk/state-machines/mem/pil/mem.pil:524-527`). This is *narrower*
than the 12-slot byte-form `Interaction.MemoryBusEntry` used downstream
by memory-load / memory-store paths through MemAlign.

For the register-bus reads-side lane match we work with the natural
6-slot shape directly:

* `MemoryBusEntry6 F` — 6-field record carrying `(as, ptr, mem_step,
  bytes, value_lo, value_hi)`, mirroring the PIL slot order verbatim.
* `memBus_row_Main_register_read_rs1 m row` — Main row's rs1
  register-read projection: pulls the `a_offset_imm0` / `a_reg_prev_mem_step`
  / `a[0]` / `a[1]` columns as the 6 slot values; pins `as = 3`,
  `bytes = 8` per the constant slots that PIL2 emits for the
  `assumes_a_reg` permutation entry (`main.pil:300`).
* `memBus_row_Main_register_read_rs2 m row` — analogous for the
  `b_offset_imm0` / `b_reg_prev_mem_step` / `b[0]` / `b[1]` columns
  (`main.pil:307`).
* `memBus_row_Main_store_reg_prev m row` — analogous for the
  `store_offset` / `store_reg_prev_mem_step` / `store_reg_prev_value[*]`
  columns (`main.pil:316`).

The slot-match lemmas in `Airs/MemoryBus/BusShape.lean` show that each
extracted spec's `slotValue` agrees pointwise with the corresponding
projection's slot. Composed against a hypothesis that the bus protocol
pins the entry's value lanes against an external `MemoryBusEntry`'s
`memory_entry_lo` / `memory_entry_hi` packed halves, the slot-match
gives the lane-match conclusion in `Airs/MemoryBus/LaneMatch.lean`
without recourse to a trivial `.symm` rewriting.

## Why a separate 6-slot type

We use a dedicated `MemoryBusEntry6` rather than reusing the 12-slot
`MemoryBusEntry`: the register-bus path doesn't traverse byte
decomposition — the 32-bit register lanes are precisely Main's `a[0]`,
`a[1]`, etc. Reusing the 12-slot type would force slot-match lemmas to
carry byte-range hypotheses irrelevant to the register-side path.

The byte-form `MemoryBusEntry` remains the native interface for
downstream memory-load / memory-store paths (LoadD / StoreD etc.).
Bridging from the 6-slot shape to the byte-form is by `memory_entry_lo`
/ `memory_entry_hi` equality on the value halves.
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks
open ZiskFv.Airs.Main

/-- 6-slot memory-bus entry shape matching the PIL emission tuple
    `[as, ptr, mem_step, bytes, value_lo, value_hi]` for register-bus
    reads. `value_lo` / `value_hi` are the two 32-bit lanes of the
    64-bit register value carried on the bus. -/
structure MemoryBusEntry6 (F : Type) [Field F] where
  as : F
  ptr : F
  mem_step : F
  bytes : F
  value_lo : F
  value_hi : F
  deriving BEq, DecidableEq, Inhabited

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Main row's rs1 register-read projection into the 6-slot register-bus
    shape. The `as`/`bytes` slots are pinned to the constants PIL emits
    (`as = 3` for register read, `bytes = 8` for a doubleword); the
    remaining slots come from the named-column accessors and the
    auxiliary columns at indices 10 (`a_offset_imm0`) and 30
    (`a_reg_prev_mem_step`).

    The `Circuit.main` references for the auxiliary columns mirror the
    extracted `bus_emission_Main_0` thunks verbatim — these columns
    are not yet exposed as named accessors on `Valid_Main`, but we
    reference them positionally so the slot-match lemma in
    `Airs/MemoryBus/BusShape.lean` reduces to a pointwise identity. -/
@[simp]
def memBus_row_Main_register_read_rs1
    (m : Valid_Main C F ExtF) (row : ℕ) : MemoryBusEntry6 F :=
  { as := 3
    ptr := Circuit.main m.circuit (id := 1) (column := 10) (row := row) (rotation := 0)
    mem_step := Circuit.main m.circuit (id := 1) (column := 30) (row := row) (rotation := 0)
    bytes := 8
    value_lo := m.a_0 row
    value_hi := m.a_1 row }

/-- Main row's rs2 register-read projection. Mirrors
    `memBus_row_Main_register_read_rs1` for the `b`-side columns: the
    auxiliary columns are 15 (`b_offset_imm0`) and 31
    (`b_reg_prev_mem_step`); the value lanes are `m.b_0` and `m.b_1`. -/
@[simp]
def memBus_row_Main_register_read_rs2
    (m : Valid_Main C F ExtF) (row : ℕ) : MemoryBusEntry6 F :=
  { as := 3
    ptr := Circuit.main m.circuit (id := 1) (column := 15) (row := row) (rotation := 0)
    mem_step := Circuit.main m.circuit (id := 1) (column := 31) (row := row) (rotation := 0)
    bytes := 8
    value_lo := m.b_0 row
    value_hi := m.b_1 row }

/-- Main row's store-reg previous-value read projection. The store-reg
    previous-value columns (33/34) and the offset / mem_step columns
    (24/32) are *not* aliased to `c_0`/`c_1` — they are auxiliary
    `store_reg_prev_value[*]` cells PIL uses to consistency-check the
    write site against the *previous* memory-bus state of register rd
    before Main's row writes its result. The write itself is emitted
    via the value's encoding into Main's `c[*]` lanes (handled
    elsewhere). -/
@[simp]
def memBus_row_Main_store_reg_prev
    (m : Valid_Main C F ExtF) (row : ℕ) : MemoryBusEntry6 F :=
  { as := 3
    ptr := Circuit.main m.circuit (id := 1) (column := 24) (row := row) (rotation := 0)
    mem_step := Circuit.main m.circuit (id := 1) (column := 32) (row := row) (rotation := 0)
    bytes := 8
    value_lo := Circuit.main m.circuit (id := 1) (column := 33) (row := row) (rotation := 0)
    value_hi := Circuit.main m.circuit (id := 1) (column := 34) (row := row) (rotation := 0) }

end ZiskFv.Airs.MemoryBus
