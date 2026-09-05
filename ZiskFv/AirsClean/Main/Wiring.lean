import Extraction.LookupWiring
import ZiskFv.AirsClean.Main.Constraints

/-!
# Main operation-bus wiring

The generated c45 link is Main's assume-side bus-5000 interaction. Its two
precompile fields retain the physical products `STEP * is_precompiled` and
`jmp_offset1 * is_precompiled`; they reduce to the live non-precompile message
only after applying the existing `is_precompiled = 0` scope.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.OperationBus (OpBusMessage)

@[reducible]
def operationExprToClean (row : Var MainRowWithRom FGL) :
    Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "2" => some 2
  | .constant "4" => some 4
  | .constant "8" => some 8
  | .constant "16" => some 16
  | .constant "32" => some 32
  | .constant "64" => some 64
  | .constant "128" => some 128
  | .constant "256" => some 256
  | .constant "512" => some 512
  | .constant "1024" => some 1024
  | .constant "2048" => some 2048
  | .constant "4096" => some 4096
  | .constant "8192" => some 8192
  | .constant "16384" => some 16384
  | .constant "32768" => some 32768
  | .constant "4194304" => some 4194304
  | .witness 1 0 0 => some row.core.a_0
  | .witness 1 1 0 => some row.core.a_1
  | .witness 1 2 0 => some row.core.b_0
  | .witness 1 3 0 => some row.core.b_1
  | .witness 1 4 0 => some row.core.c_0
  | .witness 1 5 0 => some row.core.c_1
  | .witness 1 6 0 => some row.core.flag
  | .witness 1 7 0 => some row.core.pc
  | .witness 1 8 0 => some row.rom.a_src_imm
  | .witness 1 9 0 => some row.rom.a_src_mem
  | .witness 1 10 0 => some row.rom.a_offset_imm0
  | .witness 1 11 0 => some row.rom.a_imm1
  | .witness 1 12 0 => some row.rom.is_precompiled
  | .witness 1 13 0 => some row.rom.b_src_imm
  | .witness 1 14 0 => some row.rom.b_src_mem
  | .witness 1 15 0 => some row.rom.b_offset_imm0
  | .witness 1 16 0 => some row.rom.b_imm1
  | .witness 1 17 0 => some row.rom.b_src_ind
  | .witness 1 18 0 => some row.core.ind_width
  | .witness 1 19 0 => some row.core.is_external_op
  | .witness 1 20 0 => some row.core.op
  | .witness 1 21 0 => some row.core.store_pc
  | .witness 1 22 0 => some row.rom.store_mem
  | .witness 1 23 0 => some row.rom.store_ind
  | .witness 1 24 0 => some row.rom.store_offset
  | .witness 1 25 0 => some row.core.set_pc
  | .witness 1 26 0 => some row.core.jmp_offset1
  | .witness 1 27 0 => some row.core.jmp_offset2
  | .witness 1 28 0 => some row.core.m32
  | .witness 1 35 0 => some row.rom.a_src_reg
  | .witness 1 36 0 => some row.rom.b_src_reg
  | .witness 1 37 0 => some row.rom.store_reg
  | .add (.mul (.airValue 1) (.constant "4194304")) (.fixed 1 0) =>
      some row.rom.main_step
  | .add lhs (.constant "0") => operationExprToClean row lhs
  | .add (.constant "0") rhs => operationExprToClean row rhs
  | .add lhs rhs => do
      return (← operationExprToClean row lhs) + (← operationExprToClean row rhs)
  | .sub lhs rhs => do
      return (← operationExprToClean row lhs) - (← operationExprToClean row rhs)
  | .mul lhs rhs => do
      return (← operationExprToClean row lhs) * (← operationExprToClean row rhs)
  | _ => none

@[reducible]
def operationSlotsToClean (row : Var MainRowWithRom FGL) :
    List Slot → Option (List (Expression FGL))
  | [] => some []
  | slot :: slots => do
      return (← operationExprToClean row slot.value) ::
        (← operationSlotsToClean row slots)

@[reducible]
def opBusTuple (message : OpBusMessage (Expression FGL)) : List (Expression FGL) :=
  [message.op, message.a_lo, message.a_hi, message.b_lo, message.b_hi,
    message.c_lo, message.c_hi, message.flag, message.main_step,
    message.extended_arg, message.extra_args_0]

/-- The exact physical Main operation tuple before applying the no-precompile
scope. -/
@[reducible]
def sourceOpBusMessageExpr (row : Var MainRowWithRom FGL) :
    OpBusMessage (Expression FGL) :=
  { op := row.core.op
    a_lo := row.core.a_0
    a_hi := (1 - row.core.m32) * row.core.a_1
    b_lo := row.core.b_0
    b_hi := (1 - row.core.m32) * row.core.b_1
    c_lo := row.core.c_0
    c_hi := row.core.c_1
    flag := row.core.flag
    main_step := row.rom.main_step * row.rom.is_precompiled
    extended_arg := row.core.jmp_offset1 * row.rom.is_precompiled
    extra_args_0 := 0 }

/-- The exact extraction facts carried by Main c45. -/
structure OperationWiring (row : Var MainRowWithRom FGL) where
  link : ValidatedLink
  operationHint : HintTuple
  c45Link : link = link_Main_45
  linkedHints : link.hints = [operationHint]
  linkShape : link.shape = .directAssumesNegFormZeroTail
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  operationPiop : operationHint.piop = "Lookup"
  operationBus : operationHint.busId = .constant "5000"
  operationIsAssumes : operationHint.proves = false
  operationMultiplicity : operationHint.multiplicity =
    .add (.witness 1 19 0) (.constant "0")
  multiplicityInterpretation : operationExprToClean row operationHint.multiplicity =
    some row.core.is_external_op
  slotInterpretation : operationSlotsToClean row operationHint.slots =
    some (opBusTuple (sourceOpBusMessageExpr row))

set_option maxRecDepth 10000 in
@[reducible]
def operationWiring (row : Var MainRowWithRom FGL) : OperationWiring row where
  link := link_Main_45
  operationHint := hint_Main_45_0
  c45Link := rfl
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_45
  operationPiop := rfl
  operationBus := rfl
  operationIsAssumes := rfl
  operationMultiplicity := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

/-- The physical source tuple evaluates to the current live Main message under
the existing no-precompile scope. This is a semantic equality because Clean
expressions retain multiplication by zero as syntax. -/
theorem eval_sourceOpBusMessageExpr_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL)
    (h_noPrecompile : Expression.eval env row.rom.is_precompiled = 0) :
    eval env (sourceOpBusMessageExpr row) = eval env (opBusMessageExpr row.core) := by
  rw [OpBusMessage.mk.injEq]
  simp only [sourceOpBusMessageExpr, opBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> try rfl
  · rw [h_noPrecompile, mul_zero]
  · rw [h_noPrecompile, mul_zero]
    exact ⟨rfl, trivial⟩

/-- After interpreting the exact source slots, their evaluations agree with
the live Main operation tuple in the existing no-precompile scope. -/
theorem operationWiring_liveSlotEvaluation (env : Environment FGL)
    (row : Var MainRowWithRom FGL)
    (h_noPrecompile : Expression.eval env row.rom.is_precompiled = 0) :
    (operationSlotsToClean row (operationWiring row).operationHint.slots).map
        (List.map (Expression.eval env)) =
      some (List.map (Expression.eval env) (opBusTuple (opBusMessageExpr row.core))) := by
  rw [(operationWiring row).slotInterpretation]
  simp only [Option.map_some, opBusTuple, List.map_cons, List.map_nil, Expression.eval]
  simp [h_noPrecompile]

/-- Raw AIR-value or fixed-column syntax is rejected unless it occurs in the
audited physical STEP expression. -/
theorem operationExprToClean_rejects_bare_step_parts (row : Var MainRowWithRom FGL) :
    operationExprToClean row (.airValue 1) = none
      ∧ operationExprToClean row (.fixed 1 0) = none := by
  exact ⟨rfl, rfl⟩

end ZiskFv.AirsClean.Main
