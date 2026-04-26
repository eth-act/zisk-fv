import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus

/-!
# MemoryBus.LaneMatch — promoted lane-match theorems for register bus entries

This module promotes three previously-axiomatized `def` predicates in
`Airs/MemoryBus.lean` to **theorems** derived from a structural bus-entry
matching hypothesis:

* `register_write_lanes_match_of_bus_emission` — the `c_0`/`c_1` lanes
  (register-write destination) match a given `MemoryBusEntry` when the
  entry's packed byte lanes equal the Main column values.
* `register_read_rs1_lanes_match_of_bus_emission` — the `a_0`/`a_1` lanes
  (register-read source, rs1) match the entry.
* `register_read_rs2_lanes_match_of_bus_emission` — the `b_0`/`b_1` lanes
  (register-read source, rs2) match the entry.

## Background on the memory bus

ZisK's memory bus (bus_id = 10, `vendor/zisk/pil/opids.pil:12`) carries
entries of shape `[as, ptr, mem_step, bytes, x0..x7]` for both register
reads/writes (as = 1 or 3) and memory reads/writes (as = 2). The value
payload is carried as 8 byte-level fields `x0..x7`.

For register-bus entries the value is a 64-bit register value: `x0..x3`
are the low 4 bytes and `x4..x7` are the high 4 bytes of the register.
`memory_entry_lo e = x0 + x1·256 + x2·65536 + x3·16777216` assembles the
low half; `memory_entry_hi e = x4 + x5·256 + x6·65536 + x7·16777216`
assembles the high half.

Main's PIL constraint enforces that for a register-write entry, the 32-bit
lanes `c_0`/`c_1` equal the assembled lo/hi halves respectively. Phase 2
callers establish the `h_emit` hypothesis from PIL byte-range constraints
plus the transpile axiom for the relevant opcode.

## Memory bus extraction gap

The operation bus (bus_id = 5000) uses PIL2 `lookup_*` macros whose
`gsum_debug_data` hints carry only `F`-typed slots, enabling the slot-match
derivation in `Airs/BusShape.lean`. The memory bus uses `permutation_*`
macros whose hints carry `ExtF`-typed challenge randomness; the extractor
skips these (all placeholders with `multiplicity := 0` in
`Extraction/Buses.lean`). Consequently, there is no auto-extracted
`bus_emission_Main_N` spec with non-zero multiplicity for the memory bus.

The three theorems here serve as the **interface keystone** for Phase 2: they
fix the `h_emit` parameter shape so that downstream derivation lemmas know
what structural predicate to thread from the GoldenTraces fixtures.

## h_emit parameter shape

For each theorem the `h_emit` parameter is a pair of equalities of the form

  `memory_entry_lo e = m.<lane_lo> row  ∧  memory_entry_hi e = m.<lane_hi> row`

where `<lane_lo>` / `<lane_hi>` are `c_0`/`c_1` (write), `a_0`/`a_1` (rs1
read), or `b_0`/`b_1` (rs2 read). This is the *structural* condition the PIL
memory-bus protocol enforces for the register-side entries: the 4-byte-packed
lo/hi halves of the entry's value lanes equal the Main circuit's named column
values. Phase 2 callers establish this from opcode-specific transpile axioms.
-/

namespace ZiskFv.Airs.MemoryBus.LaneMatch

open Goldilocks
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Register-write lane match from bus emission.** Promotes
    `register_write_lanes_match` from a taken-as-hypothesis `def` to a
    theorem. Given that the memory-bus register-write entry's packed byte
    lanes equal the Main row's `c_0`/`c_1` columns (`h_emit`), the
    `register_write_lanes_match` predicate follows by symmetry.

    The `h_emit` hypothesis encodes the PIL-level bus-emission contract for
    a `store_reg` entry (`as = 1, multiplicity = 1`): the entry's low/high
    4-byte halves (`memory_entry_lo`, `memory_entry_hi`) equal the Main
    circuit's result-output columns `c_0` and `c_1`.

    Phase 2 callers establish `h_emit` from the transpile axiom for the
    opcode (e.g. `transpile_ADD` pins `c_0 = lo(result)`, `c_1 = hi(result)`)
    combined with byte-range constraints that fix the byte-level decomposition
    of the result lanes in the memory-bus entry. -/
theorem register_write_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_emit : memory_entry_lo e = m.c_0 row
              ∧ memory_entry_hi e = m.c_1 row) :
    register_write_lanes_match m row e := by
  simp only [register_write_lanes_match]
  exact ⟨h_emit.1.symm, h_emit.2.symm⟩

/-- **Register-read (rs1 / a-lanes) lane match from bus emission.** Promotes
    `register_read_rs1_lanes_match` (newly added in this commit) from a
    taken-as-hypothesis `def` to a theorem.

    Given that the memory-bus register-read entry's packed byte lanes equal
    the Main row's `a_0`/`a_1` columns (`h_emit`), the
    `register_read_rs1_lanes_match` predicate follows by symmetry.

    The `h_emit` hypothesis encodes the PIL-level bus-emission contract for a
    `load_reg` entry on the `a` side (`as = 1, multiplicity = -1`): the entry's
    lo/hi packed halves equal Main's `a_0`/`a_1` columns, which PIL constrains
    to carry `xreg(rs1)` as two 32-bit lanes.

    Phase 2 callers establish `h_emit` from the transpile axiom for the opcode
    (e.g. `transpile_LD` pins `a_0 = lo(xreg rs1)`, `a_1 = hi(xreg rs1)`)
    plus the byte-level decomposition of the rs1 value in the memory-bus entry. -/
theorem register_read_rs1_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_emit : memory_entry_lo e = m.a_0 row
              ∧ memory_entry_hi e = m.a_1 row) :
    register_read_rs1_lanes_match m row e := by
  simp only [register_read_rs1_lanes_match]
  exact ⟨h_emit.1.symm, h_emit.2.symm⟩

/-- **Register-read (rs2 / b-lanes) lane match from bus emission.** Promotes
    `register_read_rs2_lanes_match` from a taken-as-hypothesis `def` to a
    theorem.

    Given that the memory-bus register-read entry's packed byte lanes equal
    the Main row's `b_0`/`b_1` columns (`h_emit`), the
    `register_read_rs2_lanes_match` predicate follows by symmetry.

    The `h_emit` hypothesis encodes the PIL-level bus-emission contract for a
    `load_reg` entry on the `b` side (`as = 1, multiplicity = -1`): the entry's
    lo/hi packed halves equal Main's `b_0`/`b_1` columns, which for store
    instructions (SD and variants) carry `xreg(rs2)` as two 32-bit lanes.

    Phase 2 callers establish `h_emit` from the transpile axiom for the opcode
    (e.g. `transpile_SD` pins `b_0 = lo(xreg rs2)`, `b_1 = hi(xreg rs2)`)
    plus the byte-level decomposition of the rs2 value in the memory-bus entry. -/
theorem register_read_rs2_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_emit : memory_entry_lo e = m.b_0 row
              ∧ memory_entry_hi e = m.b_1 row) :
    register_read_rs2_lanes_match m row e := by
  simp only [register_read_rs2_lanes_match]
  exact ⟨h_emit.1.symm, h_emit.2.symm⟩

end ZiskFv.Airs.MemoryBus.LaneMatch
