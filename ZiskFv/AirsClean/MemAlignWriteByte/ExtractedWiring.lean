import Extraction.LookupWiring
import ZiskFv.AirsClean.MemAlignWriteByte.SourceMirrorWeld

namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.DualByte (DualByteChannel)

/-- Partial interpretation of actual source syntax: unsupported lanes fail. -/
def sourceExprToClean (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) : Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "2" => some 2
  | .constant "4" => some 4
  | .constant "8" => some 8
  | .witness 1 0 0 => some row.sel_high_4b
  | .witness 1 1 0 => some row.sel_high_2b
  | .witness 1 2 0 => some row.sel_high_b
  | .witness 1 3 0 => some row.direct_value
  | .witness 1 4 0 => some row.composed_value
  | .witness 1 5 0 => some row.written_composed_value
  | .witness 1 6 0 => some row.written_byte_value
  | .witness 1 7 0 => some row.value_16b
  | .witness 1 8 0 => some row.value_8b
  | .witness 1 9 0 => some row.byte_value
  | .witness 1 10 0 => some row.addr_w
  | .witness 1 11 0 => some row.step
  | .witness 1 12 0 => some row.mem_write_values_0
  | .witness 1 13 0 => some row.mem_write_values_1
  | .airValue 0 => some padding
  | .add value (.constant "0") => sourceExprToClean row padding value
  | .add lhs rhs => return (← sourceExprToClean row padding lhs) + (← sourceExprToClean row padding rhs)
  | .sub lhs rhs => return (← sourceExprToClean row padding lhs) - (← sourceExprToClean row padding rhs)
  | .mul lhs rhs => return (← sourceExprToClean row padding lhs) * (← sourceExprToClean row padding rhs)
  | .neg value => return -(← sourceExprToClean row padding value)
  | _ => none

def decodeSourceSlots (row : Var MemAlignWriteByteRow FGL) (padding : Expression FGL)
    (slots : List Slot) : Option (List (Expression FGL)) :=
  slots.mapM fun slot => sourceExprToClean row padding slot.value

@[reducible]
def memoryMessageTuple (message : MemBusMessage (Expression FGL)) : List (Expression FGL) :=
  [message.mem_op, message.ptr, message.timestamp, message.width, message.value_0, message.value_1]

theorem alignedStoreHint_metadata :
    hint_MemAlignWriteByte_7_0.hintIndex = 1077 ∧
    hint_MemAlignWriteByte_7_0.piop = "Permutation" ∧
    hint_MemAlignWriteByte_7_0.proves = false ∧
    hint_MemAlignWriteByte_7_0.busId = Expr.constant "10" ∧
    hint_MemAlignWriteByte_7_0.multiplicity = Expr.constant "1" ∧
    hint_MemAlignWriteByte_7_0.slots.length = 6 := by
  simp [hint_MemAlignWriteByte_7_0]

theorem alignedStoreHint_mem_link : hint_MemAlignWriteByte_7_0 ∈ link_MemAlignWriteByte_7.hints := by
  simp [link_MemAlignWriteByte_7]

theorem alignedStoreHint_decode_success (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) :
    decodeSourceSlots row padding hint_MemAlignWriteByte_7_0.slots = some (memoryMessageTuple (memWriteMessageExpr row)) := by
  rfl

theorem selectedStoreHint_metadata :
    hint_MemAlignWriteByte_7_1.hintIndex = 1078 ∧
    hint_MemAlignWriteByte_7_1.piop = "Permutation" ∧
    hint_MemAlignWriteByte_7_1.proves = true ∧
    hint_MemAlignWriteByte_7_1.busId = Expr.constant "10" ∧
    hint_MemAlignWriteByte_7_1.multiplicity = Expr.constant "1" ∧
    hint_MemAlignWriteByte_7_1.slots.length = 6 := by
  simp [hint_MemAlignWriteByte_7_1]

theorem selectedStoreHint_mem_link : hint_MemAlignWriteByte_7_1 ∈ link_MemAlignWriteByte_7.hints := by
  simp [link_MemAlignWriteByte_7]

theorem selectedStoreHint_decode_success (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) :
    decodeSourceSlots row padding hint_MemAlignWriteByte_7_1.slots = some (memoryMessageTuple (memBusMessageExpr row)) := by
  rfl

theorem value16Hint_metadata :
    hint_MemAlignWriteByte_8_0.hintIndex = 1080 ∧
    hint_MemAlignWriteByte_8_0.piop = "Range Check" ∧
    hint_MemAlignWriteByte_8_0.proves = false ∧
    hint_MemAlignWriteByte_8_0.busId = Expr.constant "103" ∧
    hint_MemAlignWriteByte_8_0.multiplicity = Expr.constant "1" ∧
    hint_MemAlignWriteByte_8_0.slots.length = 1 := by
  simp [hint_MemAlignWriteByte_8_0]

theorem value16Hint_mem_link : hint_MemAlignWriteByte_8_0 ∈ link_MemAlignWriteByte_8.hints := by
  simp [link_MemAlignWriteByte_8]

theorem value16Hint_decode_success (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) :
    decodeSourceSlots row padding hint_MemAlignWriteByte_8_0.slots = some ([row.value_16b]) := by
  rfl

theorem dualByteHint_metadata :
    hint_MemAlignWriteByte_8_1.hintIndex = 1081 ∧
    hint_MemAlignWriteByte_8_1.piop = "Lookup" ∧
    hint_MemAlignWriteByte_8_1.proves = false ∧
    hint_MemAlignWriteByte_8_1.busId = Expr.constant "88" ∧
    hint_MemAlignWriteByte_8_1.multiplicity = Expr.constant "1" ∧
    hint_MemAlignWriteByte_8_1.slots.length = 2 := by
  simp [hint_MemAlignWriteByte_8_1]

theorem dualByteHint_mem_link : hint_MemAlignWriteByte_8_1 ∈ link_MemAlignWriteByte_8.hints := by
  simp [link_MemAlignWriteByte_8]

theorem dualByteHint_decode_success (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) :
    decodeSourceSlots row padding hint_MemAlignWriteByte_8_1.slots = some ([(dualByteMessageExpr row).byte_a, (dualByteMessageExpr row).byte_b]) := by
  rfl

theorem alignedLoadHint_metadata :
    hint_MemAlignWriteByte_9_0.hintIndex = 1075 ∧
    hint_MemAlignWriteByte_9_0.piop = "Permutation" ∧
    hint_MemAlignWriteByte_9_0.proves = false ∧
    hint_MemAlignWriteByte_9_0.busId = Expr.constant "10" ∧
    hint_MemAlignWriteByte_9_0.multiplicity = Expr.constant "1" ∧
    hint_MemAlignWriteByte_9_0.slots.length = 6 := by
  simp [hint_MemAlignWriteByte_9_0]

theorem alignedLoadHint_mem_link : hint_MemAlignWriteByte_9_0 ∈ link_MemAlignWriteByte_9.hints := by
  simp [link_MemAlignWriteByte_9]

theorem alignedLoadHint_decode_success (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) :
    decodeSourceSlots row padding hint_MemAlignWriteByte_9_0.slots = some (memoryMessageTuple (memReadMessageExpr row)) := by
  rfl

theorem writtenByteHint_metadata :
    hint_MemAlignWriteByte_10_0.hintIndex = 1069 ∧
    hint_MemAlignWriteByte_10_0.piop = "Range Check" ∧
    hint_MemAlignWriteByte_10_0.proves = false ∧
    hint_MemAlignWriteByte_10_0.busId = Expr.constant "107" ∧
    hint_MemAlignWriteByte_10_0.multiplicity = Expr.constant "1" ∧
    hint_MemAlignWriteByte_10_0.slots.length = 1 := by
  simp [hint_MemAlignWriteByte_10_0]

theorem writtenByteHint_mem_link : hint_MemAlignWriteByte_10_0 ∈ link_MemAlignWriteByte_10.hints := by
  simp [link_MemAlignWriteByte_10]

theorem writtenByteHint_decode_success (row : Var MemAlignWriteByteRow FGL)
    (padding : Expression FGL) :
    decodeSourceSlots row padding hint_MemAlignWriteByte_10_0.slots = some ([row.written_byte_value]) := by
  rfl

theorem constraint7_source_validated :
    templateOf link_MemAlignWriteByte_7.shape link_MemAlignWriteByte_7.alpha link_MemAlignWriteByte_7.gamma
      link_MemAlignWriteByte_7.accumulator link_MemAlignWriteByte_7.hints link_MemAlignWriteByte_7.derivedTuples = some link_MemAlignWriteByte_7.constraint :=
  link_MemAlignWriteByte_7.constraintValidated

theorem constraint8_source_validated :
    templateOf link_MemAlignWriteByte_8.shape link_MemAlignWriteByte_8.alpha link_MemAlignWriteByte_8.gamma
      link_MemAlignWriteByte_8.accumulator link_MemAlignWriteByte_8.hints link_MemAlignWriteByte_8.derivedTuples = some link_MemAlignWriteByte_8.constraint :=
  link_MemAlignWriteByte_8.constraintValidated

theorem constraint9_source_validated :
    templateOf link_MemAlignWriteByte_9.shape link_MemAlignWriteByte_9.alpha link_MemAlignWriteByte_9.gamma
      link_MemAlignWriteByte_9.accumulator link_MemAlignWriteByte_9.hints link_MemAlignWriteByte_9.derivedTuples = some link_MemAlignWriteByte_9.constraint :=
  link_MemAlignWriteByte_9.constraintValidated

theorem constraint10_source_validated :
    templateOf link_MemAlignWriteByte_10.shape link_MemAlignWriteByte_10.alpha link_MemAlignWriteByte_10.gamma
      link_MemAlignWriteByte_10.accumulator link_MemAlignWriteByte_10.hints link_MemAlignWriteByte_10.derivedTuples = some link_MemAlignWriteByte_10.constraint :=
  link_MemAlignWriteByte_10.constraintValidated

/-- Actual emitted row operations, tied above to h1075/h1077/h1078.
No Direct padding messages are counted as extra row tuples. -/
theorem memoryInteraction_roster_complete :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [ (MemBusChannel.pulled (memReadMessageExpr component.rowInputVar)).toRaw
      , (MemBusChannel.pulled (memWriteMessageExpr component.rowInputVar)).toRaw
      , (MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw ] :=
  component_interactionsWith_memBus

theorem dualByteInteraction_roster_complete :
    component.operations.interactionsWith DualByteChannel.toRaw =
      [(DualByteChannel.pulled (dualByteMessageExpr component.rowInputVar)).toRaw] :=
  component_interactionsWith_dualByte

end ZiskFv.AirsClean.MemAlignWriteByte
