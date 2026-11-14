import ZiskFv.AirsClean.MemAlignWriteByte.Segment
import ZiskFv.AirsClean.MemAlignWriteByte.SourceBoundaryWeld

namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-! These Direct links are not counted as the three row memory tuples. Each
source selector decodes to the actual physical-unused-row count, while proves
versus assumes controls its signed emission in `Segment.directMain`. -/

theorem paddingLoadHint_metadata :
    hint_MemAlignWriteByte_11_0.hintIndex = 1082 ∧
    hint_MemAlignWriteByte_11_0.piop = "Direct" ∧
    hint_MemAlignWriteByte_11_0.proves = true ∧
    hint_MemAlignWriteByte_11_0.busId = Expr.constant "10" ∧
    hint_MemAlignWriteByte_11_0.multiplicity = Expr.add (Expr.airValue 0) (Expr.constant "0") ∧
    hint_MemAlignWriteByte_11_0.slots.length = 6 := by
  simp [hint_MemAlignWriteByte_11_0]

theorem paddingLoadHint_mem_link : hint_MemAlignWriteByte_11_0 ∈ link_MemAlignWriteByte_11.hints := by
  simp [link_MemAlignWriteByte_11]

theorem paddingLoadHint_decode_success (s : Segment) (row : Var MemAlignWriteByteRow FGL) :
    decodeSourceSlots row (.const s.paddingSize) hint_MemAlignWriteByte_11_0.slots =
      some (memoryMessageTuple paddingLoadMessage) ∧
    sourceExprToClean row (.const s.paddingSize) hint_MemAlignWriteByte_11_0.multiplicity =
      some (.const s.paddingSize) := by
  exact ⟨rfl, rfl⟩

theorem constraint11_source_validated :
    templateOf link_MemAlignWriteByte_11.shape link_MemAlignWriteByte_11.alpha link_MemAlignWriteByte_11.gamma
      link_MemAlignWriteByte_11.accumulator link_MemAlignWriteByte_11.hints link_MemAlignWriteByte_11.derivedTuples = some link_MemAlignWriteByte_11.constraint :=
  link_MemAlignWriteByte_11.constraintValidated

theorem paddingSelectedStoreHint_metadata :
    hint_MemAlignWriteByte_12_0.hintIndex = 1083 ∧
    hint_MemAlignWriteByte_12_0.piop = "Direct" ∧
    hint_MemAlignWriteByte_12_0.proves = false ∧
    hint_MemAlignWriteByte_12_0.busId = Expr.constant "10" ∧
    hint_MemAlignWriteByte_12_0.multiplicity = Expr.add (Expr.airValue 0) (Expr.constant "0") ∧
    hint_MemAlignWriteByte_12_0.slots.length = 6 := by
  simp [hint_MemAlignWriteByte_12_0]

theorem paddingSelectedStoreHint_mem_link : hint_MemAlignWriteByte_12_0 ∈ link_MemAlignWriteByte_12.hints := by
  simp [link_MemAlignWriteByte_12]

theorem paddingSelectedStoreHint_decode_success (s : Segment) (row : Var MemAlignWriteByteRow FGL) :
    decodeSourceSlots row (.const s.paddingSize) hint_MemAlignWriteByte_12_0.slots =
      some (memoryMessageTuple paddingSelectedStoreMessage) ∧
    sourceExprToClean row (.const s.paddingSize) hint_MemAlignWriteByte_12_0.multiplicity =
      some (.const s.paddingSize) := by
  exact ⟨rfl, rfl⟩

theorem constraint12_source_validated :
    templateOf link_MemAlignWriteByte_12.shape link_MemAlignWriteByte_12.alpha link_MemAlignWriteByte_12.gamma
      link_MemAlignWriteByte_12.accumulator link_MemAlignWriteByte_12.hints link_MemAlignWriteByte_12.derivedTuples = some link_MemAlignWriteByte_12.constraint :=
  link_MemAlignWriteByte_12.constraintValidated

theorem paddingAlignedStoreHint_metadata :
    hint_MemAlignWriteByte_13_0.hintIndex = 1084 ∧
    hint_MemAlignWriteByte_13_0.piop = "Direct" ∧
    hint_MemAlignWriteByte_13_0.proves = true ∧
    hint_MemAlignWriteByte_13_0.busId = Expr.constant "10" ∧
    hint_MemAlignWriteByte_13_0.multiplicity = Expr.add (Expr.airValue 0) (Expr.constant "0") ∧
    hint_MemAlignWriteByte_13_0.slots.length = 6 := by
  simp [hint_MemAlignWriteByte_13_0]

theorem paddingAlignedStoreHint_mem_link : hint_MemAlignWriteByte_13_0 ∈ link_MemAlignWriteByte_13.hints := by
  simp [link_MemAlignWriteByte_13]

theorem paddingAlignedStoreHint_decode_success (s : Segment) (row : Var MemAlignWriteByteRow FGL) :
    decodeSourceSlots row (.const s.paddingSize) hint_MemAlignWriteByte_13_0.slots =
      some (memoryMessageTuple paddingAlignedStoreMessage) ∧
    sourceExprToClean row (.const s.paddingSize) hint_MemAlignWriteByte_13_0.multiplicity =
      some (.const s.paddingSize) := by
  exact ⟨rfl, rfl⟩

theorem constraint13_source_validated :
    templateOf link_MemAlignWriteByte_13.shape link_MemAlignWriteByte_13.alpha link_MemAlignWriteByte_13.gamma
      link_MemAlignWriteByte_13.accumulator link_MemAlignWriteByte_13.hints link_MemAlignWriteByte_13.derivedTuples = some link_MemAlignWriteByte_13.constraint :=
  link_MemAlignWriteByte_13.constraintValidated

/-- Checked Direct-to-channel lowering. Both tuple arity and route must be the
actual source forms; source `proves` controls the emitted sign. Unsupported
source syntax cannot silently become a zero interaction. -/
def decodeDirectInteraction (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) (hint : HintTuple) :
    Option (ChannelInteraction MemBusChannel) := do
  match hint.piop, hint.busId with
  | "Direct", .constant "10" =>
    let slots ← decodeSourceSlots row padding hint.slots
    let multiplicity ← sourceExprToClean row padding hint.multiplicity
    match slots with
    | [mem_op, ptr, timestamp, width, value_0, value_1] =>
      return MemBusChannel.emitted
        (if hint.proves then multiplicity else -multiplicity)
        { mem_op, ptr, timestamp, width, value_0, value_1 }
    | _ => none
  | _, _ => none

/-- Decoding the actual three validated source hints gives exactly the actual
once-per-segment operation roster, including its negative selected STORE. -/
theorem rawSource_direct_roster_decode
    (source : GsumBoundary.Source FGL) (row : Var MemAlignWriteByteRow FGL) :
    [hint_MemAlignWriteByte_11_0, hint_MemAlignWriteByte_12_0, hint_MemAlignWriteByte_13_0].mapM
      (decodeDirectInteraction row (.const (source.airValue 0))) =
        some (sourceDirectInteractions source) := rfl

/-- The real raw source scalar, not an honest-builder count, decodes all three
actual source selectors and tuples. Source proves/assumes metadata above fixes
their signed canonical emissions in `sourceDirectMain`. -/
theorem rawSource_direct_decode
    (source : GsumBoundary.Source FGL) (row : Var MemAlignWriteByteRow FGL) :
    decodeSourceSlots row (.const (source.airValue 0)) hint_MemAlignWriteByte_11_0.slots =
      some (memoryMessageTuple paddingLoadMessage) ∧
    decodeSourceSlots row (.const (source.airValue 0)) hint_MemAlignWriteByte_12_0.slots =
      some (memoryMessageTuple paddingSelectedStoreMessage) ∧
    decodeSourceSlots row (.const (source.airValue 0)) hint_MemAlignWriteByte_13_0.slots =
      some (memoryMessageTuple paddingAlignedStoreMessage) ∧
    sourceExprToClean row (.const (source.airValue 0)) hint_MemAlignWriteByte_11_0.multiplicity =
      some (.const (source.airValue 0)) ∧
    sourceExprToClean row (.const (source.airValue 0)) hint_MemAlignWriteByte_12_0.multiplicity =
      some (.const (source.airValue 0)) ∧
    sourceExprToClean row (.const (source.airValue 0)) hint_MemAlignWriteByte_13_0.multiplicity =
      some (.const (source.airValue 0)) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ZiskFv.AirsClean.MemAlignWriteByte
