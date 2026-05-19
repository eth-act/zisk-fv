import ZiskFv.AirsClean.MemAlignByte.Spec
import Clean.Circuit.Basic

/-!
# MemAlignByte circuit operations

The 9 F-typed constraints of ZisK's MemAlignByte AIR
(`build/extraction/Extraction/MemAlignByte.lean`):

1. `sel_high_4b * (1 - sel_high_4b) = 0`  (sel_high_4b boolean)
2. `sel_high_2b * (1 - sel_high_2b) = 0`  (sel_high_2b boolean)
3. `sel_high_b * (1 - sel_high_b) = 0`    (sel_high_b boolean)
4. composed_value definitional identity (byte-recombination)
5. `is_write * (1 - is_write) = 0`        (is_write boolean)
6. written_composed_value definitional identity (write-side byte-recombination)
7. mem_write_values_0 definition (sel_high_4b multiplexer)
8. mem_write_values_1 definition
9. bus_byte definition (is_write multiplexer)

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var MemAlignByteRow FGL) : Circuit FGL Unit := do
  assertZero (row.sel_high_4b * (1 - row.sel_high_4b))
  assertZero (row.sel_high_2b * (1 - row.sel_high_2b))
  assertZero (row.sel_high_b * (1 - row.sel_high_b))
  -- composed_value definitional identity
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
  assertZero (row.is_write * (1 - row.is_write))
  -- written_composed_value definitional identity
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
  -- mem_write_values_0 = sel_high_4b · (direct_value - written_composed_value) + written_composed_value
  assertZero (row.mem_write_values_0
    - (row.sel_high_4b * (row.direct_value - row.written_composed_value)
       + row.written_composed_value))
  -- mem_write_values_1 = sel_high_4b · (written_composed_value - direct_value) + direct_value
  assertZero (row.mem_write_values_1
    - (row.sel_high_4b * (row.written_composed_value - row.direct_value)
       + row.direct_value))
  -- bus_byte = is_write · (written_byte_value - byte_value) + byte_value
  assertZero (row.bus_byte
    - (row.is_write * (row.written_byte_value - row.byte_value) + row.byte_value))

end ZiskFv.AirsClean.MemAlignByte
