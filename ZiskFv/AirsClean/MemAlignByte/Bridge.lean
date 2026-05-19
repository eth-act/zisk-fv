import ZiskFv.AirsClean.MemAlignByte.Soundness
import ZiskFv.Airs.MemAlignByte

/-!
# `Valid_MemAlignByte` ↔ `MemAlignByteRow` compatibility

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL) (r : ℕ)
    : MemAlignByteRow FGL where
  sel_high_4b := v.sel_high_4b r
  sel_high_2b := v.sel_high_2b r
  sel_high_b := v.sel_high_b r
  direct_value := v.direct_value r
  composed_value := v.composed_value r
  written_composed_value := v.written_composed_value r
  written_byte_value := v.written_byte_value r
  value_16b := v.value_16b r
  value_8b := v.value_8b r
  byte_value := v.byte_value r
  addr_w := v.addr_w r
  step := v.step r
  is_write := v.is_write r
  mem_write_values_0 := v.mem_write_values_0 r
  mem_write_values_1 := v.mem_write_values_1 r
  bus_byte := v.bus_byte r

end ZiskFv.AirsClean.MemAlignByte
