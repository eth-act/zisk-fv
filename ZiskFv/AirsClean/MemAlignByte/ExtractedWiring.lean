import Extraction.LookupWiring
import ZiskFv.AirsClean.MemAlignByte.Circuit
import Extraction.MemAlignByte
import ZiskFv.AirsClean.DirectPadding

/-!
# Source-linked MemAlignByte aligned-read interaction

This module binds pilout hint `#1022` from generated constraint 11 to the live
aligned-read pull and hint `#1027` from generated constraint 9 to the live
selected-byte push. Generated c9 also carries conditional aligned-write hint
`#1025`, which is absent from the current two-interaction Clean component.
The AIR-value Direct padding constraints c13/c14 below have local source
equation welds only; they are not live row interactions.

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
  | .witness 1 6 0 => some row.written_byte_value
  | .witness 1 7 0 => some row.value_16b
  | .witness 1 8 0 => some row.value_8b
  | .witness 1 9 0 => some row.byte_value
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

/-! ## Explicit range and DualByte source tuples

The c10 cluster joins the 16-bit range lookup (`mem_align_byte.pil:103`)
and the exact bus-88 pair (`:104`); c12 checks the written byte (`:25`).
The compiled circuit uses the existing static tables. This does not finish
bus 88 or account for the separate segment-padding Direct updates.
-/

theorem rangeAndDualByte_source_roster :
    link_MemAlignByte_10.hints =
      [hint_MemAlignByte_10_0, hint_MemAlignByte_10_1] ∧
    link_MemAlignByte_12.hints = [hint_MemAlignByte_12_0] := ⟨rfl, rfl⟩

theorem rangeAndDualByte_constraintsValidated :
    templateOf link_MemAlignByte_10.shape link_MemAlignByte_10.alpha
        link_MemAlignByte_10.gamma link_MemAlignByte_10.accumulator
        link_MemAlignByte_10.hints link_MemAlignByte_10.derivedTuples =
      some link_MemAlignByte_10.constraint ∧
    templateOf link_MemAlignByte_12.shape link_MemAlignByte_12.alpha
        link_MemAlignByte_12.gamma link_MemAlignByte_12.accumulator
        link_MemAlignByte_12.hints link_MemAlignByte_12.derivedTuples =
      some link_MemAlignByte_12.constraint :=
  ⟨link_MemAlignByte_10.constraintValidated, link_MemAlignByte_12.constraintValidated⟩

theorem rangeAndDualByte_metadata :
    (hint_MemAlignByte_10_0.piop, hint_MemAlignByte_10_0.busId,
      hint_MemAlignByte_10_0.proves, hint_MemAlignByte_10_0.multiplicity) =
        ("Range Check", Expr.constant "103", false, Expr.constant "1") ∧
    (hint_MemAlignByte_10_1.piop, hint_MemAlignByte_10_1.busId,
      hint_MemAlignByte_10_1.proves, hint_MemAlignByte_10_1.multiplicity) =
        ("Lookup", Expr.constant "88", false, Expr.constant "1") ∧
    (hint_MemAlignByte_12_0.piop, hint_MemAlignByte_12_0.busId,
      hint_MemAlignByte_12_0.proves, hint_MemAlignByte_12_0.multiplicity) =
        ("Range Check", Expr.constant "107", false, Expr.constant "1") := ⟨rfl, rfl, rfl⟩

theorem rangeAndDualByte_decode_success (row : Var MemAlignByteRow FGL) :
    decodeReadSourceSlots row hint_MemAlignByte_10_0.slots = some [row.value_16b] ∧
    decodeReadSourceSlots row hint_MemAlignByte_10_1.slots =
      some [row.byte_value, row.value_8b] ∧
    decodeReadSourceSlots row hint_MemAlignByte_12_0.slots =
      some [row.written_byte_value] := ⟨rfl, rfl, rfl⟩

/-- Exact compiled lookup positions, not an unused message alias. The explicit
written-byte source check is unconditional, even when `is_write = 0`. -/
theorem rangeAndDualByte_compiledLookups :
    component.operations.lookups[3]? =
      some { table := (Table.fromStatic RangeTables.rangeTable16).toRaw, entry := #v[component.rowInputVar.value_16b] } ∧
    component.operations.lookups[4]? =
      some { table := (Table.fromStatic RangeTables.dualByteTable).toRaw, entry := #v[component.rowInputVar.byte_value, component.rowInputVar.value_8b] } ∧
    component.operations.lookups[5]? =
      some { table := (Table.fromStatic RangeTables.rangeTable8).toRaw, entry := #v[component.rowInputVar.written_byte_value] } := by
  rw [Component.lookups_eq]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Segment Direct padding equations (build-only source fidelity)

The producer fills zero LOAD padding rows and sets the shared AIR count
to `num_rows - padding_row` (`mem/src/mem_align_byte_sm.rs:140–147`).
Neither this equation weld nor the generated links prove that an arbitrary
exposed value is that physical count. Live segment integration is separate.
-/

theorem paddingDirect_source_roster :
    link_MemAlignByte_13.hints = [hint_MemAlignByte_13_0] ∧
    link_MemAlignByte_14.hints = [hint_MemAlignByte_14_0] := ⟨rfl, rfl⟩

theorem paddingDirect_source_metadata :
    (hint_MemAlignByte_13_0.piop, hint_MemAlignByte_13_0.busId,
      hint_MemAlignByte_13_0.proves, hint_MemAlignByte_13_0.multiplicity) =
        ("Direct", Expr.constant "10", true, Expr.add (.airValue 0) (.constant "0")) ∧
    (hint_MemAlignByte_14_0.piop, hint_MemAlignByte_14_0.busId,
      hint_MemAlignByte_14_0.proves, hint_MemAlignByte_14_0.multiplicity) =
        ("Direct", Expr.constant "10", false, Expr.add (.airValue 0) (.constant "0")) :=
  ⟨rfl, rfl⟩

theorem paddingDirect_tuple_decode (row : Var MemAlignByteRow FGL) :
    decodeReadSourceSlots row hint_MemAlignByte_13_0.slots = some [1, 0, 0, 8, 0, 0] ∧
    decodeReadSourceSlots row hint_MemAlignByte_14_0.slots = some [1, 0, 0, 1, 0, 0] :=
  ⟨rfl, rfl⟩

/-- The positive aligned-load adjustment reads count AIR value0 and
accumulator AIR value1, not any row witness. -/
theorem alignedPaddingDirect_source_iff
    {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]
    (c : C FGL FGL) (row : Nat) :
    MemAlignByte.extraction.constraint_13_every_row c row ↔
      alignedLoadPaddingEquation
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.exposed c (index := 1))
        (Extraction.Circuit.challenge c (index := 0))
        (Extraction.Circuit.challenge c (index := 1)) := Iff.rfl

/-- The byte-load subtraction shares count AIR value0 and uses accumulator
AIR value2; its sign and width differ from the positive aligned update. -/
theorem bytePaddingDirect_source_iff
    {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]
    (c : C FGL FGL) (row : Nat) :
    MemAlignByte.extraction.constraint_14_every_row c row ↔
      byteLoadPaddingEquation
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.exposed c (index := 2))
        (Extraction.Circuit.challenge c (index := 0))
        (Extraction.Circuit.challenge c (index := 1)) := Iff.rfl

end ZiskFv.AirsClean.MemAlignByte
