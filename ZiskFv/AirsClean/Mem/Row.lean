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
  -- 8 byte-lane witness columns added in C8 Phase 1.
  -- These are not extracted from PIL (Mem AIR only has value[0]/value[1] chunks
  -- per `mem.pil`); they are added on top of PIL chunks to express the
  -- byte-addressed Sail memory model on which `SailSpec/BusEffect.lean`
  -- depends. Packing constraints (`value_0 = x0+x1*256+...+x3*16777216`,
  -- analogous for `value_1`) tie them back to the extracted PIL columns;
  -- byte ranges flow from `range_bus_sound`.
  x0 : F
  x1 : F
  x2 : F
  x3 : F
  x4 : F
  x5 : F
  x6 : F
  x7 : F
deriving ProvableStruct

end ZiskFv.AirsClean.Mem
