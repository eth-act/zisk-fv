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
  | .witness 1 8 0 => some row.reg_0
  | .witness 1 9 0 => some row.reg_1
  | .witness 1 10 0 => some row.reg_2
  | .witness 1 11 0 => some row.reg_3
  | .witness 1 12 0 => some row.reg_4
  | .witness 1 13 0 => some row.reg_5
  | .witness 1 14 0 => some row.reg_6
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

/-! ## Register range tuples

`mem/pil/mem_align.pil:113–118` range-checks each register as one byte.
The c33–c35 clusters account for registers 1–6; c38 accounts for register 0.
Register 7 remains in the already-linked c36 ROM/range cluster.
-/

open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)

/-- A source range hint, its exact row expression, and its compiled negative
interaction. Membership of a static provider is a separate channel fact. -/
structure RegisterRangeWiring where
  link : ValidatedLink
  hint : HintTuple
  sourceMember : hint ∈ link.hints
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  rangePiop : hint.piop = "Range Check"
  rangeBus : hint.busId = .constant "107"
  rangeIsAssumes : hint.proves = false
  rangeMultiplicity : hint.multiplicity = .constant "1"
  source : Expression FGL
  slotInterpretation : decodeMemorySourceSlots component.rowInputVar hint.slots = some [source]
  registerIndex : Nat
  compiledInteraction :
    (component.operations.interactionsWith MemAlignRangeChannel.toRaw)[registerIndex]? =
      some ((MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr source)).toRaw)

@[reducible]
def reg1RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_33, hint_MemAlign_33_0,
    by simp [link_MemAlign_33], link_MemAlign_33.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_1, rfl, 1,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

@[reducible]
def reg2RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_33, hint_MemAlign_33_1,
    by simp [link_MemAlign_33], link_MemAlign_33.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_2, rfl, 2,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

@[reducible]
def reg3RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_34, hint_MemAlign_34_0,
    by simp [link_MemAlign_34], link_MemAlign_34.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_3, rfl, 3,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

@[reducible]
def reg4RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_34, hint_MemAlign_34_1,
    by simp [link_MemAlign_34], link_MemAlign_34.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_4, rfl, 4,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

@[reducible]
def reg5RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_35, hint_MemAlign_35_0,
    by simp [link_MemAlign_35], link_MemAlign_35.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_5, rfl, 5,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

@[reducible]
def reg6RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_35, hint_MemAlign_35_1,
    by simp [link_MemAlign_35], link_MemAlign_35.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_6, rfl, 6,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

@[reducible]
def reg0RangeWiring : RegisterRangeWiring :=
  ⟨link_MemAlign_38, hint_MemAlign_38_0,
    by simp [link_MemAlign_38], link_MemAlign_38.constraintValidated,
    rfl, rfl, rfl, rfl, component.rowInputVar.reg_0, rfl, 0,
    by rw [component_interactionsWith_memAlignRangeChannel]; rfl⟩

/-- Every hint of the four newly bound constraints is accounted for. -/
theorem registerRange_source_roster :
    link_MemAlign_33.hints = [reg1RangeWiring.hint, reg2RangeWiring.hint] ∧
    link_MemAlign_34.hints = [reg3RangeWiring.hint, reg4RangeWiring.hint] ∧
    link_MemAlign_35.hints = [reg5RangeWiring.hint, reg6RangeWiring.hint] ∧
    link_MemAlign_38.hints = [reg0RangeWiring.hint] := ⟨rfl, rfl, rfl, rfl⟩

end ZiskFv.AirsClean.MemAlign
