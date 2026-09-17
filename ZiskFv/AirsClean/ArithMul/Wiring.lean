import Extraction.LookupWiring
import ZiskFv.AirsClean.ArithMul.Circuit
import ZiskFv.AirsClean.ArithMul.ResultSlotPins

/-!
# Arith operation-bus wiring

The generated c61 link is the physical `provides_operation` interaction at
`zisk/state-machines/arith/pil/arith.pil:247-258`. In particular, slot seven
is the `div_by_zero` column; it is live for zero-divisor DIV/REM rows.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.OperationBus (OpBusMessage)

@[reducible]
def operationExprToClean : Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "65536" => some 65536
  | .witness 1 7 0 => some componentComplete.rowInputVar.chunks.a_0
  | .witness 1 8 0 => some componentComplete.rowInputVar.chunks.a_1
  | .witness 1 9 0 => some componentComplete.rowInputVar.chunks.a_2
  | .witness 1 10 0 => some componentComplete.rowInputVar.chunks.a_3
  | .witness 1 11 0 => some componentComplete.rowInputVar.chunks.b_0
  | .witness 1 12 0 => some componentComplete.rowInputVar.chunks.b_1
  | .witness 1 13 0 => some componentComplete.rowInputVar.chunks.b_2
  | .witness 1 14 0 => some componentComplete.rowInputVar.chunks.b_3
  | .witness 1 15 0 => some componentComplete.rowInputVar.chunks.c_0
  | .witness 1 16 0 => some componentComplete.rowInputVar.chunks.c_1
  | .witness 1 17 0 => some componentComplete.rowInputVar.chunks.c_2
  | .witness 1 18 0 => some componentComplete.rowInputVar.chunks.c_3
  | .witness 1 19 0 => some componentComplete.rowInputVar.chunks.d_0
  | .witness 1 20 0 => some componentComplete.rowInputVar.chunks.d_1
  | .witness 1 29 0 => some componentComplete.rowInputVar.flags.div
  | .witness 1 33 0 => some componentComplete.rowInputVar.flags.main_div
  | .witness 1 34 0 => some componentComplete.rowInputVar.flags.main_mul
  | .witness 1 36 0 => some componentComplete.rowInputVar.flags.div_by_zero
  | .witness 1 39 0 => some componentComplete.rowInputVar.flags.op
  | .witness 1 40 0 => some componentComplete.rowInputVar.flags.bus_res1
  | .witness 1 41 0 => some componentComplete.rowInputVar.flags.multiplicity
  | .add lhs (.constant "0") => operationExprToClean lhs
  | .add (.constant "0") rhs => operationExprToClean rhs
  | .add lhs rhs => do return (← operationExprToClean lhs) + (← operationExprToClean rhs)
  | .sub lhs rhs => do return (← operationExprToClean lhs) - (← operationExprToClean rhs)
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

/-- The exact extraction and live-model facts carried by Arith c61. -/
structure OperationWiring where
  link : ValidatedLink
  operationHint : HintTuple
  c61Link : link = link_Arith_61
  linkedHints : link.hints = [operationHint]
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  operationPiop : operationHint.piop = "Lookup"
  operationBus : operationHint.busId = .constant "5000"
  operationIsProves : operationHint.proves = true
  operationMultiplicity : operationHint.multiplicity =
    .add (.witness 1 41 0) (.constant "0")
  multiplicityInterpretation : operationExprToClean operationHint.multiplicity =
    some componentComplete.rowInputVar.flags.multiplicity
  slotInterpretation : operationSlotsToClean operationHint.slots =
    some (opBusTuple (primaryOpBusMessageExpr componentComplete.rowInputVar))

set_option maxRecDepth 10000 in
@[reducible]
def operationWiring : OperationWiring where
  link := link_Arith_61
  operationHint := hint_Arith_61_0
  c61Link := rfl
  linkedHints := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Arith_61
  operationPiop := rfl
  operationBus := rfl
  operationIsProves := rfl
  operationMultiplicity := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

/-- On MUL-family rows the source-faithful flag reduces to zero from the
existing Arith scope constraint; callers do not supply a new flag premise. -/
theorem operationFlag_eq_zero_of_mul_mode (row : ArithMulRow FGL)
    (h_scope : DivScopeSpec row) (h_div : row.flags.div = 0) :
    row.flags.div_by_zero = 0 := by
  simpa [h_div] using h_scope.1

end ZiskFv.AirsClean.ArithMul
