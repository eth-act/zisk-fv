import ZiskFv.AirsClean.MemAlign.Bridge

/-!
# Source-linked MemAlign memory interaction

The MemAlign ROM consumer is already fully bound in `Bridge`: pilout hint
`#998` belongs to generated `link_MemAlign_36`, uses bus 133, and decodes its
six slots to the live ROM message. The component's cyclic D3 transition proves
that the row-local `delta_pc` is the source hint's successor-PC difference, and
`component_interactionsWith_memAlignRomChannel` pins the negative emission.

The next unbound MemAlign route is hint `#1001`, the memory-bus permutation in
generated constraint 37. This module binds its exact six source slots and
symbolic multiplicity to the live `mainWithMemBusAndMemAlignRomAndRanges`
interaction. Decoding returns `none` for unsupported syntax; the source binding
proves a concrete `some` result.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- Checked interpretation of the source syntax used by MemAlign hint #1001. -/
def memorySourceExprToClean (row : Var MemAlignRow FGL) :
    Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "8" => some 8
  | .witness 1 0 0 => some row.addr
  | .witness 1 1 0 => some row.offset
  | .witness 1 2 0 => some row.width
  | .witness 1 3 0 => some row.wr
  | .witness 1 6 0 => some row.sel_up_to_down
  | .witness 1 7 0 => some row.sel_down_to_up
  | .witness 1 24 0 => some row.step
  | .witness 1 26 0 => some row.sel_prove
  | .witness 1 27 0 => some row.value_0
  | .witness 1 28 0 => some row.value_1
  | .add value (.constant "0") => memorySourceExprToClean row value
  | .add lhs rhs =>
      return (← memorySourceExprToClean row lhs) + (← memorySourceExprToClean row rhs)
  | .sub lhs rhs =>
      return (← memorySourceExprToClean row lhs) - (← memorySourceExprToClean row rhs)
  | .mul lhs rhs =>
      return (← memorySourceExprToClean row lhs) * (← memorySourceExprToClean row rhs)
  | .neg value => return -(← memorySourceExprToClean row value)
  | _ => none

def decodeMemorySourceSlots (row : Var MemAlignRow FGL) (slots : List Slot) :
    Option (List (Expression FGL)) :=
  slots.mapM fun slot => memorySourceExprToClean row slot.value

@[reducible]
def memBusMessageTuple (message : MemBusMessage (Expression FGL)) :
    List (Expression FGL) :=
  [message.mem_op, message.ptr, message.timestamp, message.width,
    message.value_0, message.value_1]

/-- Hint #1001 is source-linked through the checked c37 direct template. -/
theorem memoryHint_mem_link : hint_MemAlign_37_0 ∈ link_MemAlign_37.hints := by
  simp [link_MemAlign_37]

theorem memoryLink_constraintValidated :
    templateOf link_MemAlign_37.shape link_MemAlign_37.alpha
        link_MemAlign_37.gamma link_MemAlign_37.accumulator
        link_MemAlign_37.hints link_MemAlign_37.derivedTuples =
      some link_MemAlign_37.constraint :=
  link_MemAlign_37.constraintValidated

/-- Pin the actual pilout route: `Permutation`, proves side, bus 10, with the
    source selector difference as multiplicity. -/
theorem memoryHint_metadata :
    hint_MemAlign_37_0.hintIndex = 1001 ∧
      hint_MemAlign_37_0.piop = "Permutation" ∧
      hint_MemAlign_37_0.proves = true ∧
      hint_MemAlign_37_0.busId = Expr.constant "10" ∧
      hint_MemAlign_37_0.multiplicity =
        Expr.sub (Expr.witness 1 26 0)
          (Expr.add (Expr.witness 1 6 0) (Expr.witness 1 7 0)) := by
  simp [hint_MemAlign_37_0]

/-- The symbolic source multiplicity is exactly the live interaction
    multiplicity. -/
theorem memoryMultiplicity_decode_success (row : Var MemAlignRow FGL) :
    memorySourceExprToClean row hint_MemAlign_37_0.multiplicity =
      some (row.sel_prove - selAssumeExpr row) := by
  rfl

/-- All six source slots decode successfully in the live memory-message order. -/
theorem memoryHint_decode_success (row : Var MemAlignRow FGL) :
    decodeMemorySourceSlots row hint_MemAlign_37_0.slots =
      some (memBusMessageTuple (memBusMessageExpr row)) := by
  rfl

/-- The decoded source tuple and multiplicity are the actual interaction
    emitted by the live MemAlign component. -/
theorem memoryInteraction_mem_component_operations :
    ((MemBusChannel.emitted
        (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
        (memBusMessageExpr component.rowInputVar)).toRaw) ∈
      component.operations.interactionsWith MemBusChannel.toRaw := by
  rw [component_interactionsWith_memBus]
  simp

/-- There are no further live MemAlign memory interactions: the complete
    roster is the single c37-derived interaction above. -/
theorem memoryInteraction_roster_complete :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [((MemBusChannel.emitted
          (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
          (memBusMessageExpr component.rowInputVar)).toRaw)] :=
  component_interactionsWith_memBus

end ZiskFv.AirsClean.MemAlign
