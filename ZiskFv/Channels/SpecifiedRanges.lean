import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Field.Goldilocks

/-!
# SpecifiedRanges slice channel

The full `SpecifiedRanges` AIR is not yet extracted. This module models only
the bus-103, 16-bit slice used by Mem's constraint-linked range hints. The
provider component owns the static lookup; this channel names the matching
cross-AIR interaction and its constructive membership guarantee.
-/

namespace ZiskFv.Channels.SpecifiedRanges

open Goldilocks
open ZiskFv.AirsClean.RangeTables

/-- The two-slot range-check message: upstream range id and checked value. -/
structure SpecifiedRangeMessage (F : Type) where
  rangeId : F
  value : F
deriving ProvableStruct

/-- The `Range Check` hint bus used by Mem's 16-bit distance chunks. -/
def memDistanceRangeId : FGL := 103

/-- The source-linked static slice of the not-yet-extracted `SpecifiedRanges`
AIR. `mem.pil:267-268` uses bus 103 for these 16-bit values. -/
instance SpecifiedRangesSliceChannel : Channel FGL SpecifiedRangeMessage where
  name := "SpecifiedRangesSlice103"
  Guarantees msg _ :=
    msg.rangeId = memDistanceRangeId ∧ rangeTable16.Spec msg.value

/-- The value-level bus-103 message for one Mem distance chunk. -/
@[reducible]
def memDistanceMessage {F : Type} [OfNat F 103] (value : F) : SpecifiedRangeMessage F :=
  { rangeId := 103, value }

/-- Channel membership on the bus-103 slice is exactly the 16-bit static
range predicate. -/
theorem memDistanceMessage_guarantees_iff (value : FGL) (data : ProverData FGL) :
    SpecifiedRangesSliceChannel.Guarantees (memDistanceMessage value) data ↔
      rangeTable16.Spec value := by
  simp [SpecifiedRangesSliceChannel, memDistanceMessage, memDistanceRangeId]

/-- The `Range Check` hint bus used by Main's three register-step distances.

`main.pil:333-335` emits `range_check(<slot>_mem_step - <slot>_reg_prev_mem_step - 1, min: 0,
max: MAX_RANGE)` for the a, b and store register slots, with `MAX_RANGE = (1 << 24) - 1`. The
pinned extraction puts all three on bus **102**
(`build/extraction/Extraction/LookupWiring.lean` `hint_Main_40_1`, and `constraint_Main_41` for the
b / store twins). -/
def registerStepRangeId : FGL := 102

/-- The source-linked static slice of the bus-102 range check.

This is the **descent** the register MemBus telescope needs. Without it
`<slot>_reg_prev_mem_step` is a free witness column, balance admits register access *cycles*
disjoint from `RegisterBoundary.bootMessage`, and a register read is unconstrained. See
`ZiskFv/AirsClean/RegisterStepRangeSlice.lean`. -/
instance RegisterStepRangeChannel : Channel FGL SpecifiedRangeMessage where
  name := "SpecifiedRangesSlice102"
  Guarantees msg _ :=
    msg.rangeId = registerStepRangeId ∧ rangeTable24.Spec msg.value

/-- The value-level bus-102 message for one register-step distance. -/
@[reducible]
def registerStepMessage {F : Type} [OfNat F 102] (value : F) : SpecifiedRangeMessage F :=
  { rangeId := 102, value }

/-- Channel membership on the bus-102 slice is exactly the 24-bit static range predicate. -/
theorem registerStepMessage_guarantees_iff (value : FGL) (data : ProverData FGL) :
    RegisterStepRangeChannel.Guarantees (registerStepMessage value) data ↔
      rangeTable24.Spec value := by
  simp [RegisterStepRangeChannel, registerStepMessage, registerStepRangeId]

end ZiskFv.Channels.SpecifiedRanges
