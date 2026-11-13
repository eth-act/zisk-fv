import Extraction.LookupWiring
import ZiskFv.AirsClean.BinaryAdd.Circuit

/-!
# BinaryAdd operation-bus wiring

The generated c5 link joins the last 16-bit range lookup with BinaryAdd's
bus-5000 provider tuple. This module binds that exact provider hint to the
Clean operation message. Unsupported manifest syntax has no interpretation.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.OperationBus (OpBusMessage)

@[reducible]
def operationExprToClean : Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "10" => some 10
  | .constant "65536" => some 65536
  | .witness 1 0 0 => some component.rowInputVar.a_0
  | .witness 1 1 0 => some component.rowInputVar.a_1
  | .witness 1 2 0 => some component.rowInputVar.b_0
  | .witness 1 3 0 => some component.rowInputVar.b_1
  | .witness 1 4 0 => some component.rowInputVar.c_chunks_0
  | .witness 1 5 0 => some component.rowInputVar.c_chunks_1
  | .witness 1 6 0 => some component.rowInputVar.c_chunks_2
  | .witness 1 7 0 => some component.rowInputVar.c_chunks_3
  | .add lhs (.constant "0") => operationExprToClean lhs
  | .add (.constant "0") rhs => operationExprToClean rhs
  | .add lhs rhs => do return (← operationExprToClean lhs) + (← operationExprToClean rhs)
  | .mul lhs rhs => do return (← operationExprToClean lhs) * (← operationExprToClean rhs)
  | _ => none

@[reducible]
def operationSlotsToClean : List Slot → Option (List (Expression FGL))
  | [] => some []
  | slot :: slots => do
      return (← operationExprToClean slot.value) :: (← operationSlotsToClean slots)

@[reducible]
def opBusTuple (message : OpBusMessage (Expression FGL)) : List (Expression FGL) :=
  [message.op, message.a_lo, message.a_hi, message.b_lo, message.b_hi,
    message.c_lo, message.c_hi, message.flag, message.main_step,
    message.extended_arg, message.extra_args_0]

/-- The exact source and live-model facts carried by BinaryAdd c5. -/
structure OperationWiring where
  link : ValidatedLink
  rangeHint : HintTuple
  operationHint : HintTuple
  c5Link : link = link_BinaryAdd_5
  linkedHints : link.hints = [rangeHint, operationHint]
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  operationPiop : operationHint.piop = "Lookup"
  operationBus : operationHint.busId = .constant "5000"
  operationIsProves : operationHint.proves = true
  operationMultiplicity : operationHint.multiplicity = .constant "1"
  slotInterpretation : operationSlotsToClean operationHint.slots =
    some (opBusTuple (opBusMessageExpr component.rowInputVar))

@[reducible]
def operationWiring : OperationWiring where
  link := link_BinaryAdd_5
  rangeHint := hint_BinaryAdd_5_0
  operationHint := hint_BinaryAdd_5_1
  c5Link := rfl
  linkedHints := rfl
  constraintValidated := ValidatedLink.constraintValidated link_BinaryAdd_5
  operationPiop := rfl
  operationBus := rfl
  operationIsProves := rfl
  operationMultiplicity := rfl
  slotInterpretation := rfl

/-! ## Result-chunk range lookups

`binary/pil/binary_add.pil:21–22` checks both chunks of each limb.
The c4 cluster carries chunks 1 and 2; c6 carries chunk 0. The c5
operation link above retains chunk 3. These are static range lookups in
the compiled component, not a claim that bus 103 has been composed.
-/

/-- One checked source range tuple and its actual compiled static lookup. -/
structure ChunkRangeWiring where
  link : ValidatedLink
  hint : HintTuple
  sourceMember : hint ∈ link.hints
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  rangePiop : hint.piop = "Range Check"
  rangeBus : hint.busId = .constant "103"
  rangeIsAssumes : hint.proves = false
  rangeMultiplicity : hint.multiplicity = .constant "1"
  source : Expression FGL
  slotInterpretation : operationSlotsToClean hint.slots = some [source]
  lookupIndex : Nat
  compiledLookup : component.operations.lookups[lookupIndex]? =
    some { table := (Table.fromStatic RangeTables.rangeTable16).toRaw, entry := #v[source] }

@[reducible]
def chunk1RangeWiring : ChunkRangeWiring where
  link := link_BinaryAdd_4
  hint := hint_BinaryAdd_4_0
  sourceMember := by simp [link_BinaryAdd_4]
  constraintValidated := link_BinaryAdd_4.constraintValidated
  rangePiop := rfl
  rangeBus := rfl
  rangeIsAssumes := rfl
  rangeMultiplicity := rfl
  source := component.rowInputVar.c_chunks_1
  slotInterpretation := rfl
  lookupIndex := 5
  compiledLookup := by rw [Component.lookups_eq]; rfl

@[reducible]
def chunk2RangeWiring : ChunkRangeWiring where
  link := link_BinaryAdd_4
  hint := hint_BinaryAdd_4_1
  sourceMember := by simp [link_BinaryAdd_4]
  constraintValidated := link_BinaryAdd_4.constraintValidated
  rangePiop := rfl
  rangeBus := rfl
  rangeIsAssumes := rfl
  rangeMultiplicity := rfl
  source := component.rowInputVar.c_chunks_2
  slotInterpretation := rfl
  lookupIndex := 6
  compiledLookup := by rw [Component.lookups_eq]; rfl

@[reducible]
def chunk0RangeWiring : ChunkRangeWiring where
  link := link_BinaryAdd_6
  hint := hint_BinaryAdd_6_0
  sourceMember := by simp [link_BinaryAdd_6]
  constraintValidated := link_BinaryAdd_6.constraintValidated
  rangePiop := rfl
  rangeBus := rfl
  rangeIsAssumes := rfl
  rangeMultiplicity := rfl
  source := component.rowInputVar.c_chunks_0
  slotInterpretation := rfl
  lookupIndex := 4
  compiledLookup := by rw [Component.lookups_eq]; rfl

/-- Both hints in c4 are accounted for, in their source order. -/
theorem chunkRange_c4_roster :
    link_BinaryAdd_4.hints =
      [chunk1RangeWiring.hint, chunk2RangeWiring.hint] := rfl

/-- The c6 hint is exactly the component's first result-chunk lookup. -/
theorem chunkRange_c6_roster :
    link_BinaryAdd_6.hints = [chunk0RangeWiring.hint] := rfl

/-- The historical opcode mutation cannot be interpreted as BinaryAdd's live
operation tuple. -/
theorem operationExprToClean_rejects_wrong_opcode :
    operationExprToClean (.constant "11") = none := by rfl

end ZiskFv.AirsClean.BinaryAdd
