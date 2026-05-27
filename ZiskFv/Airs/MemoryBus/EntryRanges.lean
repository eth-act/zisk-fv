import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.RangeBusSoundness

/-!
# Memory-bus entry chunk-range soundness

The memory-bus protocol carries entries whose 2 32-bit chunks
(`value_0, value_1`) participate in a lookup-argument range guarantee
that they fit in `[0, 2^32)`. At the PIL level the underlying
participants declare their packing components as `bits(8)`:

PIL citations:
* `zisk/state-machines/mem/pil/mem.pil:64`: `col witness bits(8) value[BYTES]`
  for the per-byte memory-data columns on the Mem AIR provider side.
* `zisk/state-machines/mem_align/pil/mem_align.pil:103`: `col witness
  bits(8) value[BYTES]` on the MemAlign* providers.
* `zisk/state-machines/main/pil/main.pil:78`: `col witness bits(8)
  x[BYTES]` on Main when participating as a memory-bus consumer.

When the participants pack their byte columns into the chunk-shaped
bus emission (`mem.pil:436`: `...value` is a 2-element 32-bit chunk
array per `permutation_proves`), the resulting chunks are bounded by
`2^32 - 1`. The lookup-argument chain across these participants
guarantees every memory-bus entry that ever appears on the bus
(load-side or store-side) has its 2 chunk cells constrained to
`[0, 2^32)`.

Trust class: lookup-argument soundness on the standard byte-range
bus, composed up to chunk granularity, restricted to memory-bus
participants.
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks
open ZiskFv.Channels.RangeBusSoundness

/-- **Memory-bus entry chunk-range soundness (derived).** Every
    memory-bus entry's 2 chunk cells (`value_0, value_1`) lie in
    `[0, 2^32)`. Soundness derives from the bus protocol's `bits(8)`
    annotations on the underlying per-byte columns of every memory-bus
    participant (Mem, MemAlign*, Main's memory-bus emission path),
    composed into 32-bit chunks via the PIL packing.

    The row argument to `range_bus_sound` is dummied to `0` since
    `MemoryBusEntry` is not a row-indexed record. -/
theorem memory_bus_entry_chunks_range_perm_sound
    (e : Interaction.MemoryBusEntry FGL) :
    memory_entry_chunks_in_range e := by
  refine ⟨?_, ?_⟩
  · exact range_bus_sound e (fun e _ => e.value_0) 32 trivial 0
  · exact range_bus_sound e (fun e _ => e.value_1) 32 trivial 0

/-- The lo-half chunk `e.value_0` fits in `[0, 2^32)`.
    Direct projection from `memory_bus_entry_chunks_range_perm_sound`;
    lets JAL / JALR / AUIPC discharge the `h_lo_bound` parameter their
    canonicals previously asked the caller to supply. -/
theorem memory_entry_lo_val_lt_2_32 (e : Interaction.MemoryBusEntry FGL) :
    (memory_entry_lo e).val < 4294967296 :=
  (memory_bus_entry_chunks_range_perm_sound e).1

end ZiskFv.Airs.MemoryBus
