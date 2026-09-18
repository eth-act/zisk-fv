import Extraction.LookupWiring
import ZiskFv.AirsClean.MemAlignReadByte.Circuit

/-!
# Source-linked MemAlignReadByte memory interactions

`fullRv64imSoundEnsemble` includes the live `MemAlignReadByte.component`. This
module binds its complete two-operation memory roster to pilout hints `#1049`
and `#1050`, validated by generated constraints 5 and 6 respectively.

Every source expression is decoded through `Option`; unsupported syntax cannot
silently become a live zero lane.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- Checked interpretation of the source syntax used by hints #1049 and #1050. -/
def memorySourceExprToClean (row : Var MemAlignReadByteRow FGL) :
    Expr → Option (Expression FGL)
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
  | .witness 1 7 0 => some row.byte_value
  | .witness 1 8 0 => some row.addr_w
  | .witness 1 9 0 => some row.step
  | .add value (.constant "0") => memorySourceExprToClean row value
  | .add lhs rhs =>
      return (← memorySourceExprToClean row lhs) + (← memorySourceExprToClean row rhs)
  | .sub lhs rhs =>
      return (← memorySourceExprToClean row lhs) - (← memorySourceExprToClean row rhs)
  | .mul lhs rhs =>
      return (← memorySourceExprToClean row lhs) * (← memorySourceExprToClean row rhs)
  | .neg value => return -(← memorySourceExprToClean row value)
  | _ => none

def decodeMemorySourceSlots (row : Var MemAlignReadByteRow FGL) (slots : List Slot) :
    Option (List (Expression FGL)) :=
  slots.mapM fun slot => memorySourceExprToClean row slot.value

@[reducible]
def memoryMessageTuple (message : MemBusMessage (Expression FGL)) :
    List (Expression FGL) :=
  [message.mem_op, message.ptr, message.timestamp, message.width,
    message.value_0, message.value_1]

/-! ## Aligned-read consumer -/

theorem readHint_mem_link :
    hint_MemAlignReadByte_5_0 ∈ link_MemAlignReadByte_5.hints := by
  simp [link_MemAlignReadByte_5]

theorem readLink_constraintValidated :
    templateOf link_MemAlignReadByte_5.shape link_MemAlignReadByte_5.alpha
        link_MemAlignReadByte_5.gamma link_MemAlignReadByte_5.accumulator
        link_MemAlignReadByte_5.hints link_MemAlignReadByte_5.derivedTuples =
      some link_MemAlignReadByte_5.constraint :=
  link_MemAlignReadByte_5.constraintValidated

theorem readHint_metadata :
    hint_MemAlignReadByte_5_0.hintIndex = 1049 ∧
      hint_MemAlignReadByte_5_0.piop = "Permutation" ∧
      hint_MemAlignReadByte_5_0.proves = false ∧
      hint_MemAlignReadByte_5_0.busId = Expr.constant "10" ∧
      hint_MemAlignReadByte_5_0.multiplicity = Expr.constant "1" ∧
      hint_MemAlignReadByte_5_0.slots.length = 6 := by
  simp [hint_MemAlignReadByte_5_0]

theorem readHint_decode_success (row : Var MemAlignReadByteRow FGL) :
    decodeMemorySourceSlots row hint_MemAlignReadByte_5_0.slots =
      some (memoryMessageTuple (memReadMessageExpr row)) := by
  rfl

theorem readInteraction_mem_component_operations :
    ((MemBusChannel.pulled (memReadMessageExpr component.rowInputVar)).toRaw) ∈
      component.operations.interactionsWith MemBusChannel.toRaw := by
  rw [component_interactionsWith_memBus]
  simp

/-! ## Selected-byte provider -/

theorem selectedByteHint_mem_link :
    hint_MemAlignReadByte_6_0 ∈ link_MemAlignReadByte_6.hints := by
  simp [link_MemAlignReadByte_6]

theorem selectedByteLink_constraintValidated :
    templateOf link_MemAlignReadByte_6.shape link_MemAlignReadByte_6.alpha
        link_MemAlignReadByte_6.gamma link_MemAlignReadByte_6.accumulator
        link_MemAlignReadByte_6.hints link_MemAlignReadByte_6.derivedTuples =
      some link_MemAlignReadByte_6.constraint :=
  link_MemAlignReadByte_6.constraintValidated

theorem selectedByteHint_metadata :
    hint_MemAlignReadByte_6_0.hintIndex = 1050 ∧
      hint_MemAlignReadByte_6_0.piop = "Permutation" ∧
      hint_MemAlignReadByte_6_0.proves = true ∧
      hint_MemAlignReadByte_6_0.busId = Expr.constant "10" ∧
      hint_MemAlignReadByte_6_0.multiplicity = Expr.constant "1" ∧
      hint_MemAlignReadByte_6_0.slots.length = 6 := by
  simp [hint_MemAlignReadByte_6_0]

theorem selectedByteHint_decode_success (row : Var MemAlignReadByteRow FGL) :
    decodeMemorySourceSlots row hint_MemAlignReadByte_6_0.slots =
      some (memoryMessageTuple (memBusMessageExpr row)) := by
  rfl

theorem selectedByteInteraction_mem_component_operations :
    ((MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw) ∈
      component.operations.interactionsWith MemBusChannel.toRaw := by
  rw [component_interactionsWith_memBus]
  simp

/-- The component has exactly the source-linked c5 read and c6 selected-byte
    operations on memory bus 10. -/
theorem memoryInteraction_roster_complete :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [ ((MemBusChannel.pulled (memReadMessageExpr component.rowInputVar)).toRaw)
      , ((MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw) ] :=
  component_interactionsWith_memBus

end ZiskFv.AirsClean.MemAlignReadByte
