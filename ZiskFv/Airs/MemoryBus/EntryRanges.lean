import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.MemoryBus

/-!
# Memory-bus entry byte-range soundness

The memory-bus protocol carries entries whose 8 byte cells
(`x0..x7`) participate in a row-level `bits(8)` lookup against the
standard byte-range bus. The `pil2-compiler` translates each
`bits(8)` annotation into a lookup-argument interaction on
`RANGE_BUS_ID`; lookup-argument soundness on that bus IS the trust
assumption (same trust class as the existing per-AIR range axioms
`binary_columns_in_range`, `binary_extension_columns_in_range`,
`binary_add_columns_in_range`, `main_columns_in_range`).

PIL citations:
* `zisk/state-machines/mem/pil/mem.pil:64`: `col witness bits(8) value[BYTES]`
  for the 8 per-byte memory-data columns on the Mem AIR provider side.
* `zisk/state-machines/mem_align/pil/mem_align.pil:103`: `col witness
  bits(8) value[BYTES]` on the MemAlign* providers.
* `zisk/state-machines/main/pil/main.pil:78`: `col witness bits(8)
  x[BYTES]` on Main when participating as a memory-bus consumer.

The lookup-argument chain across these participants means every
memory-bus entry that ever appears on the bus (load-side or
store-side) has its 8 byte cells constrained to `[0, 256)`. This is
the same closure pattern already accepted for register-write entries
via `memory_bus_register_write_perm_sound`.

Trust class: lookup-argument soundness on the standard byte-range
bus, restricted to memory-bus participants.
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks

/-- **Memory-bus entry byte-range soundness.** Every memory-bus
    entry's 8 byte cells (`x0..x7`) lie in `[0, 256)`. Soundness
    derives from the bus protocol's `bits(8)` annotation on the
    per-byte columns of every memory-bus participant (Mem, MemAlign*,
    Main's memory-bus emission path).

    Same trust class as `memory_bus_register_write_perm_sound`:
    a permutation-soundness-style closure on the memory bus that
    asserts every entry appearing on the bus carries the per-byte
    range constraint. -/
axiom memory_bus_entry_byte_range_perm_sound (e : Interaction.MemoryBusEntry FGL) :
    memory_entry_bytes_in_range e

end ZiskFv.Airs.MemoryBus
