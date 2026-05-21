import ZiskFv.AirsClean.MemAlignByte.Spec
import Clean.Circuit.Basic
import ZiskFv.Channels.MemAlignBus

/-!
# MemAlignByte circuit operations (the `main` field of the Component)

The 9 F-typed constraints of ZisK's MemAlignByte AIR
(`build/extraction/Extraction/MemAlignByte.lean`) followed by the
memory-bus proves-side `push`:

1. `sel_high_4b * (1 - sel_high_4b) = 0`  (sel_high_4b boolean)
2. `sel_high_2b * (1 - sel_high_2b) = 0`  (sel_high_2b boolean)
3. `sel_high_b * (1 - sel_high_b) = 0`    (sel_high_b boolean)
4. composed_value definitional identity (byte-recombination)
5. `is_write * (1 - is_write) = 0`        (is_write boolean)
6. written_composed_value definitional identity (write-side byte-recombination)
7. mem_write_values_0 definition (sel_high_4b multiplexer)
8. mem_write_values_1 definition
9. bus_byte definition (is_write multiplexer)

Then the memory-bus emission: MemAlignByte pushes its narrow-load
tuple `[mem_op, main_addr, step, 1, bus_byte, 0]` onto
`bus_id = 10 = MEMORY_ID` (`mem_align_byte.pil:96`,
`permutation_proves`). Reconstructed from the proves-side
`gsum_debug_data` hint (`bus_emission_MemAlignByte_2` in
`build/extraction/Extraction/MemoryBuses.lean`); slot-for-slot
faithful to it. The two assumes-side emissions (the paired aligned
read/write against `Mem`) and the two inert `Direct` range-check
emissions (`multiplicity = 0`) are not part of this provider's
push.

AUTO-GENERATABLE by `tools/pil-extract` (`clean-component`
subcommand, memory-bus extension) — this hand-written file is the
cross-check reference; see `docs/fv/extractor-notes.md`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks
open Circuit (assertZero)
open ZiskFv.Channels.MemAlignBus (MemAlignBusChannel)

/-- The 9 F-constraints and memory-bus push, taking the row's slot
    values as `Expression FGL`s. Returns `Unit` (MemAlignByte is a
    pure assertion — no fresh witnesses introduced inside the
    circuit). -/
@[circuit_norm]
def main (row : Var MemAlignByteRow FGL) : Circuit FGL Unit := do
  -- constraint 0 (mem/pil/mem_align_byte.pil:35)
  assertZero (row.sel_high_4b * (1 - row.sel_high_4b))
  -- constraint 1 (mem/pil/mem_align_byte.pil:36)
  assertZero (row.sel_high_2b * (1 - row.sel_high_2b))
  -- constraint 2 (mem/pil/mem_align_byte.pil:37)
  assertZero (row.sel_high_b * (1 - row.sel_high_b))
  -- constraint 3 (mem/pil/mem_align_byte.pil:59) composed_value definitional identity
  assertZero (row.composed_value
    - (row.byte_value *
        (16777216 * row.sel_high_2b * row.sel_high_b
         + 65536 * row.sel_high_2b * (1 - row.sel_high_b)
         + 256 * (1 - row.sel_high_2b) * row.sel_high_b
         + (1 - row.sel_high_2b) * (1 - row.sel_high_b))
       + row.value_8b *
        (16777216 * row.sel_high_2b * (1 - row.sel_high_b)
         + 65536 * row.sel_high_2b * row.sel_high_b
         + 256 * (1 - row.sel_high_2b) * (1 - row.sel_high_b)
         + (1 - row.sel_high_2b) * row.sel_high_b)
       + row.value_16b *
        (65536 * (1 - row.sel_high_2b) + row.sel_high_2b)))
  -- constraint 4 (mem/pil/mem_align_byte.pil:71)
  assertZero (row.is_write * (1 - row.is_write))
  -- constraint 5 (mem/pil/mem_align_byte.pil:83) written_composed_value definitional identity
  assertZero (row.written_composed_value
    - (row.written_byte_value *
        (16777216 * row.sel_high_2b * row.sel_high_b
         + 65536 * row.sel_high_2b * (1 - row.sel_high_b)
         + 256 * (1 - row.sel_high_2b) * row.sel_high_b
         + (1 - row.sel_high_2b) * (1 - row.sel_high_b))
       + row.value_8b *
        (16777216 * row.sel_high_2b * (1 - row.sel_high_b)
         + 65536 * row.sel_high_2b * row.sel_high_b
         + 256 * (1 - row.sel_high_2b) * (1 - row.sel_high_b)
         + (1 - row.sel_high_2b) * row.sel_high_b)
       + row.value_16b *
        (65536 * (1 - row.sel_high_2b) + row.sel_high_2b)))
  -- constraint 6 (mem/pil/mem_align_byte.pil:87)
  -- mem_write_values_0 = sel_high_4b · (direct_value - written_composed_value) + written_composed_value
  assertZero (row.mem_write_values_0
    - (row.sel_high_4b * (row.direct_value - row.written_composed_value)
       + row.written_composed_value))
  -- constraint 7 (mem/pil/mem_align_byte.pil:88)
  -- mem_write_values_1 = sel_high_4b · (written_composed_value - direct_value) + direct_value
  assertZero (row.mem_write_values_1
    - (row.sel_high_4b * (row.written_composed_value - row.direct_value)
       + row.direct_value))
  -- constraint 8 (mem/pil/mem_align_byte.pil:95)
  -- bus_byte = is_write · (written_byte_value - byte_value) + byte_value
  assertZero (row.bus_byte
    - (row.is_write * (row.written_byte_value - row.byte_value) + row.byte_value))
  -- Memory-bus emission: MemAlignByte pushes its narrow-load tuple onto
  -- memory bus 10 (mem_align_byte.pil:96, `permutation_proves`).
  -- Reconstructed from the proves-side `gsum_debug_data` hint
  -- (`bus_emission_MemAlignByte_2`); slot-for-slot faithful to it.
  MemAlignBusChannel.push
    { mem_op := 1 + row.is_write
      addr := row.addr_w * 8
        + (4 * row.sel_high_4b + 2 * row.sel_high_2b + row.sel_high_b)
      step := row.step
      width := 1
      value_0 := row.bus_byte
      value_1 := 0 }

/-- The elaborated circuit for MemAlignByte's `main` — 9 `assertZero`
    constraints + the memory-bus push, no fresh witnesses
    (`localLength = 0`, `unit` output). Lives here (next to `main`)
    rather than in `Circuit.lean` so the completeness axiom
    (`Completeness.lean`, whose type mentions this) can be declared
    without an import cycle. -/
@[reducible] def memAlignByteElaborated : ElaboratedCircuit FGL MemAlignByteRow unit where
  name := "MemAlignByte"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemAlignBusChannel.toRaw]

end ZiskFv.AirsClean.MemAlignByte
