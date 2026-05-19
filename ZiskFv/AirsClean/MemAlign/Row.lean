import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# MemAlign row type (Clean ProvableStruct)

The 19-slot witness layout for ZisK's MemAlign AIR (full unaligned-
access shim). Mirrors `Valid_MemAlign`'s named columns minus stage-2
accumulators.

PIL: `zisk/state-machines/mem/pil/mem_align.pil`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

structure MemAlignRow (F : Type) where
  addr : F
  offset : F
  width : F
  wr : F
  pc : F
  reset : F
  sel_up_to_down : F
  sel_down_to_up : F
  reg_0 : F
  reg_1 : F
  reg_2 : F
  reg_3 : F
  reg_4 : F
  reg_5 : F
  reg_6 : F
  reg_7 : F
  sel_0 : F
  sel_1 : F
  step : F
  sel_2 : F
  sel_3 : F
  sel_4 : F
  sel_5 : F
  sel_6 : F
  sel_7 : F
  sel_prove : F
  preL1 : F
deriving ProvableStruct

end ZiskFv.AirsClean.MemAlign
