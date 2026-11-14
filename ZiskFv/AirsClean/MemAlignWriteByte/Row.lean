import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-! The fourteen stage-1 columns of `MemAlignByte(read := 0, write := 1)`.
Column order is the generated `Extraction.MemAlignWriteByte` order, 0--13.
There is no `is_write` or `bus_byte` witness in this specialization. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte

open Goldilocks

structure MemAlignWriteByteRow (F : Type) where
  sel_high_4b : F
  sel_high_2b : F
  sel_high_b : F
  direct_value : F
  composed_value : F
  written_composed_value : F
  written_byte_value : F
  value_16b : F
  value_8b : F
  byte_value : F
  addr_w : F
  step : F
  mem_write_values_0 : F
  mem_write_values_1 : F
deriving ProvableStruct

end ZiskFv.AirsClean.MemAlignWriteByte
