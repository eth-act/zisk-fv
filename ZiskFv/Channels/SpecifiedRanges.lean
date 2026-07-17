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

end ZiskFv.Channels.SpecifiedRanges
