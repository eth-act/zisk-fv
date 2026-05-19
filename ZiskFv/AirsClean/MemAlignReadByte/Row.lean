import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# MemAlignReadByte row type (Clean ProvableStruct)

The 10-slot witness layout for ZisK's MemAlignReadByte AIR (read-only
unaligned byte-load shim). Mirrors `Valid_MemAlignReadByte`'s named
columns minus the stage-2 accumulators (`gsum`, `im_*`).

PIL citations: `zisk/state-machines/mem/pil/mem_align_byte.pil:32-65`.

## Trust note

No axiom added — pure data definition. Soundness proof (constraints
→ Spec) is a follow-up; bridges to existing `Valid_MemAlignReadByte`
via `Bridge.lean`.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

/-- 10-column witness row for MemAlignReadByte. -/
structure MemAlignReadByteRow (F : Type) where
  sel_high_4b : F
  sel_high_2b : F
  sel_high_b : F
  direct_value : F
  composed_value : F
  value_16b : F
  value_8b : F
  byte_value : F
  addr_w : F
  step : F
deriving ProvableStruct

end ZiskFv.AirsClean.MemAlignReadByte
