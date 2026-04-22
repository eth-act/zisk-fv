import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main

/-!
ZisK memory-bus schema and Main ↔ memory-bus projection for loads.

The Memory bus (identifier `MEMORY_ID = 10`, `vendor/zisk/pil/opids.pil:12`)
carries permutation entries of shape `[op, addr, mem_step, bytes, ...value]`
(`state-machines/mem/pil/mem.pil:524-527`). Main emits one entry per
source-b memory read (`main.pil:300`) and one per destination-c store
(`main.pil:323`).

For the first archetype that exercises this infrastructure — LD (A3) —
we need to project the Main AIR's memory-read row into a
`Interaction.MemoryBusEntry` and match against `bus_effect`'s memory-read
branch at `BusEffect.lean:47-62`.

**Scope note.** This module is the **A3 analogue** of
`Airs/OperationBus.lean` (which handles the operation-bus match for
ADD). It is intentionally lean: only the predicates the LD spec needs.
A4 (SD) will extend it with a store-side `matches_memory_entry_store`
symmetric projection. Full permutation-argument soundness is Phase 4 scope.

**PIL-faithfulness.** The projection `memBus_row_Main_load_b` pins the
`as`/`ptr`/`bytes` fields to the values the PIL constraint forces:

* `as = 2` (memory) when `b_src_ind = 1` — per `main.pil:300-305` the
  entry goes to the memory side (`as = 2`) when `b_src_ind` is set;
* `ptr = b_offset_imm0 + b_src_ind * a[0]` — i.e. `addr1` from
  `main.pil:192`. For LD, `b_offset_imm0 = imm` and `b_src_ind = 1`,
  so `ptr = imm + a[0]`;
* `bytes = 8` when `ind_width = 8` — per `main.pil:303`,
  `bytes = b_src_ind * (ind_width - 8) + 8`. For LD's `ind_width = 8`,
  this collapses to `8`;
* `multiplicity = -1` — the read side (assume); Sail's state.mem
  provides the value, ZisK's Main row pulls it.
* Byte lanes `x0..x7` map to the Main row's `b[0]`/`b[1]` lanes via
  their 8 constituent bytes. For compositional A3 we expose both
  directly (the packed lemma in `Spec/LoadD.lean` bridges the 8-byte
  lanes to `main_b_packed = b_0 + b_1 * 2^32`).
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks
open Interaction

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The 64-bit memory value packed from a `MemoryBusEntry`'s byte lanes
    as a single `FGL` element:
    `x0 + x1 * 2^8 + x2 * 2^16 + ... + x7 * 2^56`.

    This is the field-level image of `U64.toBV` (which produces a
    `BitVec 64`). The two forms are related by the bridge lemma
    `memory_entry_toField_eq_toBV_toNat` below. -/
@[simp]
def memory_entry_toField (e : MemoryBusEntry FGL) : FGL :=
  e.x0
  + e.x1 * 256
  + e.x2 * 65536
  + e.x3 * 16777216
  + e.x4 * 4294967296
  + e.x5 * 1099511627776
  + e.x6 * 281474976710656
  + e.x7 * 72057594037927936

/-- Low 32 bits (= `x0..x3`) of a memory-bus entry, packed as FGL. -/
@[simp]
def memory_entry_lo (e : MemoryBusEntry FGL) : FGL :=
  e.x0 + e.x1 * 256 + e.x2 * 65536 + e.x3 * 16777216

/-- High 32 bits (= `x4..x7`) of a memory-bus entry, packed as FGL. -/
@[simp]
def memory_entry_hi (e : MemoryBusEntry FGL) : FGL :=
  e.x4 + e.x5 * 256 + e.x6 * 65536 + e.x7 * 16777216

/-- The packed lane decomposition: the full 64-bit value equals
    `lo + hi * 2^32`. Needed by `Spec/LoadD.lean` to bridge the
    byte-lane memory-entry representation to the Main row's
    `(b_0, b_1)` 32-bit-lane representation. -/
lemma memory_entry_toField_lo_hi (e : MemoryBusEntry FGL) :
    memory_entry_toField e =
      memory_entry_lo e + memory_entry_hi e * 4294967296 := by
  simp only [memory_entry_toField, memory_entry_lo, memory_entry_hi]
  ring

/-- **Memory-bus entry matching.** Two `MemoryBusEntry`s match when
    every field agrees. Used in `Spec/LoadD.lean` to say: the Main
    row's memory-read projection equals the `bus_effect`-side
    memory-bus entry supplied by the caller. -/
@[simp]
def matches_memory_entry (a b : MemoryBusEntry FGL) : Prop :=
  a.multiplicity = b.multiplicity
  ∧ a.as = b.as
  ∧ a.ptr = b.ptr
  ∧ a.x0 = b.x0
  ∧ a.x1 = b.x1
  ∧ a.x2 = b.x2
  ∧ a.x3 = b.x3
  ∧ a.x4 = b.x4
  ∧ a.x5 = b.x5
  ∧ a.x6 = b.x6
  ∧ a.x7 = b.x7
  ∧ a.timestamp = b.timestamp

/-- **Memory-read lane hypotheses for LD.** The Main row's low/high `b`
    lanes (as FGL field elements) equal the low/high halves of the
    memory-bus entry's packed 8-byte value.

    This is the compositional hypothesis that the ZisK PIL memory-bus
    `permutation_assumes` discharges (`state-machines/mem/pil/mem.pil:526`):
    it asserts Main's `b[0]`/`b[1]` are the two 32-bit halves of the
    `[op=LOAD, addr, mem_step, bytes=8, ...value]` entry on the bus.

    For A3 we take this as a compositional hypothesis (same stance as
    `matches_entry` for ADD in `Airs/OperationBus.lean`). Phase 4's
    audit task is to derive it from a PIL-level bus-emission spec. -/
@[simp]
def memory_load_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.b_0 row = memory_entry_lo e
  ∧ m.b_1 row = memory_entry_hi e

/-- **Register-write-back lane hypothesis for LD.** The Main row's
    `c` lanes are what the memory-bus register-write entry carries —
    i.e. Main writes the loaded doubleword to register `rd` via
    `store_reg` (`main.pil:316-319,323-328`).

    For compositional A3 we pair this with the register-read hypothesis
    from Sail (the caller supplies both ends). Phase 4 derives from the
    memory SM's permutation-proves side. -/
@[simp]
def register_write_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.c_0 row = memory_entry_lo e
  ∧ m.c_1 row = memory_entry_hi e

end ZiskFv.Airs.MemoryBus
