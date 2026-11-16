import Extraction.LookupWiring
import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import Extraction.MemAlignReadByte
import ZiskFv.AirsClean.DirectPadding

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
  | .witness 1 5 0 => some row.value_16b
  | .witness 1 6 0 => some row.value_8b
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

/-! ## Explicit range and DualByte cluster

Source `mem/pil/mem_align_byte.pil:103–104`, specialized with read=1,
write=0. This is the local static-table interpretation of both c4 hints;
it is not a bus-88 finished-channel proof.
-/

theorem rangeAndDualByte_source_roster :
    link_MemAlignReadByte_4.hints =
      [hint_MemAlignReadByte_4_0, hint_MemAlignReadByte_4_1] := rfl

theorem rangeAndDualByte_constraintValidated :
    templateOf link_MemAlignReadByte_4.shape link_MemAlignReadByte_4.alpha
        link_MemAlignReadByte_4.gamma link_MemAlignReadByte_4.accumulator
        link_MemAlignReadByte_4.hints link_MemAlignReadByte_4.derivedTuples =
      some link_MemAlignReadByte_4.constraint :=
  link_MemAlignReadByte_4.constraintValidated

theorem rangeAndDualByte_metadata :
    (hint_MemAlignReadByte_4_0.piop, hint_MemAlignReadByte_4_0.busId,
      hint_MemAlignReadByte_4_0.proves, hint_MemAlignReadByte_4_0.multiplicity) =
        ("Range Check", Expr.constant "103", false, Expr.constant "1") ∧
    (hint_MemAlignReadByte_4_1.piop, hint_MemAlignReadByte_4_1.busId,
      hint_MemAlignReadByte_4_1.proves, hint_MemAlignReadByte_4_1.multiplicity) =
        ("Lookup", Expr.constant "88", false, Expr.constant "1") := ⟨rfl, rfl⟩

theorem rangeAndDualByte_decode_success (row : Var MemAlignReadByteRow FGL) :
    decodeMemorySourceSlots row hint_MemAlignReadByte_4_0.slots = some [row.value_16b] ∧
    decodeMemorySourceSlots row hint_MemAlignReadByte_4_1.slots =
      some [row.byte_value, row.value_8b] := ⟨rfl, rfl⟩

theorem rangeAndDualByte_compiledLookups :
    component.operations.lookups[1]? =
      some { table := (Table.fromStatic RangeTables.rangeTable16).toRaw, entry := #v[component.rowInputVar.value_16b] } ∧
    component.operations.lookups[2]? =
      some { table := (Table.fromStatic RangeTables.dualByteTable).toRaw, entry := #v[component.rowInputVar.byte_value, component.rowInputVar.value_8b] } := by
  rw [Component.lookups_eq]
  exact ⟨rfl, rfl⟩

/-! ## Segment Direct padding equations (build-only source fidelity)

`mem_align_byte.pil:106–118`, specialized with read=1/write=0, uses the
same positive aligned-load and negative byte-load updates. The producer's
count is `num_rows - padding_row` (`mem_align_byte_sm.rs:212–219`).
The exact source equations below do not identify arbitrary AIR values with
that physical count or add segment contributions to the Clean ensemble.
-/

theorem paddingDirect_source_roster :
    link_MemAlignReadByte_7.hints = [hint_MemAlignReadByte_7_0] ∧
    link_MemAlignReadByte_8.hints = [hint_MemAlignReadByte_8_0] := ⟨rfl, rfl⟩

theorem paddingDirect_source_metadata :
    (hint_MemAlignReadByte_7_0.piop, hint_MemAlignReadByte_7_0.busId,
      hint_MemAlignReadByte_7_0.proves, hint_MemAlignReadByte_7_0.multiplicity) =
        ("Direct", Expr.constant "10", true, Expr.add (.airValue 0) (.constant "0")) ∧
    (hint_MemAlignReadByte_8_0.piop, hint_MemAlignReadByte_8_0.busId,
      hint_MemAlignReadByte_8_0.proves, hint_MemAlignReadByte_8_0.multiplicity) =
        ("Direct", Expr.constant "10", false, Expr.add (.airValue 0) (.constant "0")) :=
  ⟨rfl, rfl⟩

theorem paddingDirect_tuple_decode (row : Var MemAlignReadByteRow FGL) :
    decodeMemorySourceSlots row hint_MemAlignReadByte_7_0.slots = some [1, 0, 0, 8, 0, 0] ∧
    decodeMemorySourceSlots row hint_MemAlignReadByte_8_0.slots = some [1, 0, 0, 1, 0, 0] :=
  ⟨rfl, rfl⟩

theorem alignedPaddingDirect_source_iff
    {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]
    (c : C FGL FGL) (row : Nat) :
    MemAlignReadByte.extraction.constraint_7_every_row c row ↔
      alignedLoadPaddingEquation
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.exposed c (index := 1))
        (Extraction.Circuit.challenge c (index := 0))
        (Extraction.Circuit.challenge c (index := 1)) := Iff.rfl

theorem bytePaddingDirect_source_iff
    {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]
    (c : C FGL FGL) (row : Nat) :
    MemAlignReadByte.extraction.constraint_8_every_row c row ↔
      byteLoadPaddingEquation
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.exposed c (index := 2))
        (Extraction.Circuit.challenge c (index := 0))
        (Extraction.Circuit.challenge c (index := 1)) := Iff.rfl

end ZiskFv.AirsClean.MemAlignReadByte
