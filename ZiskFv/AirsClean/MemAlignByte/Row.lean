import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# MemAlignByte row type (Clean ProvableStruct)

The 16-slot witness layout for ZisK's MemAlignByte AIR (read+write
unaligned byte-access shim). Mirrors `Valid_MemAlignByte`'s named
columns minus the stage-2 accumulators.

PIL: `zisk/state-machines/mem/pil/mem_align_byte.pil:32-90`.

## Trust note

No axiom added — pure data definition. Soundness in follow-up.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks

structure MemAlignByteRow (F : Type) where
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
  is_write : F
  mem_write_values_0 : F
  mem_write_values_1 : F
  bus_byte : F
deriving ProvableStruct

end ZiskFv.AirsClean.MemAlignByte
