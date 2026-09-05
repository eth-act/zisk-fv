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

/-- The historical opcode mutation cannot be interpreted as BinaryAdd's live
operation tuple. -/
theorem operationExprToClean_rejects_wrong_opcode :
    operationExprToClean (.constant "11") = none := by rfl

end ZiskFv.AirsClean.BinaryAdd
