import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# Mem row type (Clean ProvableStruct)

The 13-slot witness layout for ZisK's Mem AIR (memory provider).
Mirrors `Valid_Mem`'s named columns minus stage-2 accumulators.

PIL: `zisk/state-machines/mem/pil/mem.pil`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

structure MemRow (F : Type) where
  addr : F
  step : F
  sel : F
  addr_changes : F
  step_dual : F
  sel_dual : F
  value_0 : F
  value_1 : F
  wr : F
  previous_step : F
  increment_0 : F
  increment_1 : F
  read_same_addr : F
deriving ProvableStruct

end ZiskFv.AirsClean.Mem
