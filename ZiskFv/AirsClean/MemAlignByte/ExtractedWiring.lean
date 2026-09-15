import Extraction.LookupWiring
import ZiskFv.AirsClean.MemAlignByte.Circuit

/-!
# Source-linked MemAlignByte aligned-read interaction

This module binds pilout hint `#1022` from generated constraint 11 to the live
aligned-read pull and hint `#1027` from generated constraint 9 to the live
selected-byte push. Generated c9 also carries conditional aligned-write hint
`#1025`, which is absent from the current two-interaction Clean component; this
module makes no claim about that route or the AIR-value `Direct` protocol hints
in c13/c14.

Every accepted source expression decodes through `Option`; unsupported syntax
cannot silently become a zero-valued live lane.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- Checked interpretation of the source syntax used by hint #1022. -/
def readSourceExprToClean (row : Var MemAlignByteRow FGL) :
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
  | .witness 1 10 0 => some row.addr_w
  | .witness 1 11 0 => some row.step
  | .witness 1 12 0 => some row.is_write
  | .witness 1 15 0 => some row.bus_byte
  | .add value (.constant "0") => readSourceExprToClean row value
  | .add lhs rhs =>
      return (← readSourceExprToClean row lhs) + (← readSourceExprToClean row rhs)
  | .sub lhs rhs =>
      return (← readSourceExprToClean row lhs) - (← readSourceExprToClean row rhs)
  | .mul lhs rhs =>
      return (← readSourceExprToClean row lhs) * (← readSourceExprToClean row rhs)
  | .neg value => return -(← readSourceExprToClean row value)
  | _ => none

def decodeReadSourceSlots (row : Var MemAlignByteRow FGL) (slots : List Slot) :
    Option (List (Expression FGL)) :=
  slots.mapM fun slot => readSourceExprToClean row slot.value

@[reducible]
def readMessageTuple (message : MemBusMessage (Expression FGL)) :
    List (Expression FGL) :=
  [message.mem_op, message.ptr, message.timestamp, message.width,
    message.value_0, message.value_1]

/-- Hint #1022 is one of the actual source tuples checked by c11. -/
theorem readHint_mem_link : hint_MemAlignByte_11_0 ∈ link_MemAlignByte_11.hints := by
  simp [link_MemAlignByte_11]

theorem readLink_constraintValidated :
    templateOf link_MemAlignByte_11.shape link_MemAlignByte_11.alpha
        link_MemAlignByte_11.gamma link_MemAlignByte_11.accumulator
        link_MemAlignByte_11.hints link_MemAlignByte_11.derivedTuples =
      some link_MemAlignByte_11.constraint :=
  link_MemAlignByte_11.constraintValidated

/-- Pin direction, bus, multiplicity, and arity from pilout. -/
theorem readHint_metadata :
    hint_MemAlignByte_11_0.hintIndex = 1022 ∧
      hint_MemAlignByte_11_0.piop = "Permutation" ∧
      hint_MemAlignByte_11_0.proves = false ∧
      hint_MemAlignByte_11_0.busId = Expr.constant "10" ∧
      hint_MemAlignByte_11_0.multiplicity = Expr.constant "1" ∧
      hint_MemAlignByte_11_0.slots.length = 6 := by
  simp [hint_MemAlignByte_11_0]

/-- The exact source slot order is the live aligned-read message. -/
theorem readHint_decode_success (row : Var MemAlignByteRow FGL) :
    decodeReadSourceSlots row hint_MemAlignByte_11_0.slots =
      some (readMessageTuple (memReadMessageExpr row)) := by
  rfl

/-- The decoded source tuple is the actual negative memory interaction of the
    live MemAlignByte component. -/
theorem readInteraction_mem_component_operations :
    ((MemBusChannel.pulled (memReadMessageExpr component.rowInputVar)).toRaw) ∈
      component.operations.interactionsWith MemBusChannel.toRaw := by
  rw [component_interactionsWith_memBus]
  simp

/-! ## Selected-byte provider -/

/-- Hint #1027 is the proves-side source tuple checked together with the
    conditional write tuple by generated c9. -/
theorem selectedByteHint_mem_link :
    hint_MemAlignByte_9_1 ∈ link_MemAlignByte_9.hints := by
  simp [link_MemAlignByte_9]

theorem selectedByteLink_constraintValidated :
    templateOf link_MemAlignByte_9.shape link_MemAlignByte_9.alpha
        link_MemAlignByte_9.gamma link_MemAlignByte_9.accumulator
        link_MemAlignByte_9.hints link_MemAlignByte_9.derivedTuples =
      some link_MemAlignByte_9.constraint :=
  link_MemAlignByte_9.constraintValidated

theorem selectedByteHint_metadata :
    hint_MemAlignByte_9_1.hintIndex = 1027 ∧
      hint_MemAlignByte_9_1.piop = "Permutation" ∧
      hint_MemAlignByte_9_1.proves = true ∧
      hint_MemAlignByte_9_1.busId = Expr.constant "10" ∧
      hint_MemAlignByte_9_1.multiplicity = Expr.constant "1" ∧
      hint_MemAlignByte_9_1.slots.length = 6 := by
  simp [hint_MemAlignByte_9_1]

theorem selectedByteHint_decode_success (row : Var MemAlignByteRow FGL) :
    decodeReadSourceSlots row hint_MemAlignByte_9_1.slots =
      some (readMessageTuple (memBusMessageExpr row)) := by
  rfl

theorem selectedByteInteraction_mem_component_operations :
    ((MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw) ∈
      component.operations.interactionsWith MemBusChannel.toRaw := by
  rw [component_interactionsWith_memBus]
  simp

/-- The current live MemAlignByte memory roster is exhaustive: exactly the
    c11 aligned-read pull and c9 selected-byte push. In particular it contains
    no third operation for c9's conditional aligned-write hint #1025. -/
theorem memoryInteraction_roster_complete :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [ ((MemBusChannel.pulled (memReadMessageExpr component.rowInputVar)).toRaw)
      , ((MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw) ] :=
  component_interactionsWith_memBus

end ZiskFv.AirsClean.MemAlignByte
