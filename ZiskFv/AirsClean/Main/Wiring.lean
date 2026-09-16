import Extraction.LookupWiring
import ZiskFv.AirsClean.Main.Constraints
import ZiskFv.AirsClean.RegisterBoundary

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
open ZiskFv.Channels.MemoryBus (MemBusMessage)

@[reducible]
def operationExprToClean (row : Var MainRowWithRom FGL) :
    Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "2" => some 2
  | .constant "3" => some 3
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
  | .witness 1 29 0 => some row.rom.addr1
  | .witness 1 30 0 => some row.rom.a_reg_prev_mem_step
  | .witness 1 31 0 => some row.rom.b_reg_prev_mem_step
  | .witness 1 32 0 => some row.rom.store_reg_prev_mem_step
  | .witness 1 33 0 => some row.rom.store_reg_prev_value_0
  | .witness 1 34 0 => some row.rom.store_reg_prev_value_1
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

/-- PIL's physical spelling of the b-side distance keeps the timestamp as
`(1 + 4 * STEP) + 1`; the live component folds the two constants to `2`. -/
@[reducible]
def sourceBRegStepDistanceExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  ((1 + 4 * row.rom.main_step) + 1) - row.rom.b_reg_prev_mem_step - 1

/-- PIL's physical spelling of the store-side distance keeps the timestamp as
`(1 + 4 * STEP) + 2`; the live component folds the two constants to `3`. -/
@[reducible]
def sourceCRegStepDistanceExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  ((1 + 4 * row.rom.main_step) + 2) - row.rom.store_reg_prev_mem_step - 1

/-- The generated c41 cluster is exactly the pair of b- and store-side
bus-102 register-step range checks emitted by the live Main component. -/
structure RegisterStepRangeWiring (row : Var MainRowWithRom FGL) where
  link : ValidatedLink
  bHint : HintTuple
  cHint : HintTuple
  c41Link : link = link_Main_41
  linkedHints : link.hints = [bHint, cHint]
  linkShape : link.shape = .cluster2
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  bPiop : bHint.piop = "Range Check"
  cPiop : cHint.piop = "Range Check"
  bBus : bHint.busId = .constant "102"
  cBus : cHint.busId = .constant "102"
  bIsAssumes : bHint.proves = false
  cIsAssumes : cHint.proves = false
  bMultiplicityInterpretation :
    operationExprToClean row bHint.multiplicity = some row.rom.b_src_reg
  cMultiplicityInterpretation :
    operationExprToClean row cHint.multiplicity = some row.rom.store_reg
  bSlotInterpretation : operationSlotsToClean row bHint.slots =
    some [sourceBRegStepDistanceExpr row]
  cSlotInterpretation : operationSlotsToClean row cHint.slots =
    some [sourceCRegStepDistanceExpr row]

set_option maxRecDepth 10000 in
@[reducible]
def registerStepRangeWiring (row : Var MainRowWithRom FGL) :
    RegisterStepRangeWiring row where
  link := link_Main_41
  bHint := hint_Main_41_0
  cHint := hint_Main_41_1
  c41Link := rfl
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_41
  bPiop := rfl
  cPiop := rfl
  bBus := rfl
  cBus := rfl
  bIsAssumes := rfl
  cIsAssumes := rfl
  bMultiplicityInterpretation := rfl
  cMultiplicityInterpretation := rfl
  bSlotInterpretation := rfl
  cSlotInterpretation := rfl

/-- The exact c41 b-side source slot evaluates to the live range message. -/
theorem eval_sourceBRegStepDistanceExpr_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    Expression.eval env (sourceBRegStepDistanceExpr row) =
      Expression.eval env (bRegStepDistanceExpr row) := by
  simp only [Expression.eval]
  ring

/-- The exact c41 store-side source slot evaluates to the live range message. -/
theorem eval_sourceCRegStepDistanceExpr_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    Expression.eval env (sourceCRegStepDistanceExpr row) =
      Expression.eval env (cRegStepDistanceExpr row) := by
  simp only [Expression.eval]
  ring

/-- Raw AIR-value or fixed-column syntax is rejected unless it occurs in the
audited physical STEP expression. -/
theorem operationExprToClean_rejects_bare_step_parts (row : Var MainRowWithRom FGL) :
    operationExprToClean row (.airValue 1) = none
      ∧ operationExprToClean row (.fixed 1 0) = none := by
  exact ⟨rfl, rfl⟩

/-! ## Register reload wiring -/

abbrev ReloadRows :=
  Fin 31 → Var ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL

/-- The component-owned register address is substituted exactly as
`RegisterBoundary`'s fixed schema does; the three reload cells remain the
component's live row variables. -/
@[reducible]
def reloadRowAt (rows : ReloadRows) (index : Fin 31) :
    Var ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  { reg := Expression.const ((index.val + 1 : Nat) : FGL)
    reloadTimestamp := (rows index).reloadTimestamp
    reloadValue_0 := (rows index).reloadValue_0
    reloadValue_1 := (rows index).reloadValue_1 }

@[reducible]
def reloadTuple (message : MemBusMessage (Expression FGL)) : List (Expression FGL) :=
  [message.mem_op, message.ptr, message.timestamp, message.width,
    message.value_0, message.value_1]

@[reducible]
def expectedReloadSlots (index : Fin 31) : List Slot :=
  [ { name := "3", value := .constant "3" }
  , { name := toString (index.val + 1), value := .constant (toString (index.val + 1)) }
  , { name := s!"Main.last_reg_mem_step[{index.val}]",
      value := .add (.airValue (70 + index.val)) (.constant "0") }
  , { name := "8", value := .constant "8" }
  , { name := s!"Main.last_reg_value[{index.val}][0]",
      value := .add (.airValue (8 + 2 * index.val)) (.constant "0") }
  , { name := s!"Main.last_reg_value[{index.val}][1]",
      value := .add (.airValue (9 + 2 * index.val)) (.constant "0") } ]

@[reducible]
def reloadExprToClean (rows : ReloadRows) (register : Fin 31) :
    Expr → Option (Expression FGL)
  | .constant value =>
      if value = "3" then some 3
      else if value = "8" then some 8
      else if value = toString (register.val + 1) then
        some (Expression.const ((register.val + 1 : Nat) : FGL))
      else none
  | .airValue index =>
      if index = 70 + register.val then some (rows register).reloadTimestamp
      else if index = 8 + 2 * register.val then some (rows register).reloadValue_0
      else if index = 9 + 2 * register.val then some (rows register).reloadValue_1
      else none
  | .add value (.constant "0") => reloadExprToClean rows register value
  | _ => none

@[reducible]
def reloadSlotsToClean (rows : ReloadRows) (register : Fin 31) :
    List Slot → Option (List (Expression FGL))
  | [] => some []
  | slot :: slots => do
      return (← reloadExprToClean rows register slot.value) ::
        (← reloadSlotsToClean rows register slots)

theorem reloadLink_one_hint (index : Fin 31) :
    (link_Main_reload index).hints.length = 1 := by
  fin_cases index <;> rfl

@[reducible]
def reloadHint (index : Fin 31) : HintTuple :=
  (link_Main_reload index).hints[0]'(by rw [reloadLink_one_hint index]; decide)

/-- One quantified witness covers all 31 generated reload constraints. The
slot equality pins both each pilout name and the air-value expression carrying
that name; `reloadSlotsToClean` then ties those values to the modeled
`RegisterBoundary` reload message. -/
structure ReloadWiring (rows : ReloadRows) (index : Fin 31) where
  linkShape : (link_Main_reload index).shape = .direct
  constraintValidated :
    templateOf (link_Main_reload index).shape
      (link_Main_reload index).alpha (link_Main_reload index).gamma
      (link_Main_reload index).accumulator (link_Main_reload index).hints
      (link_Main_reload index).derivedTuples = some (link_Main_reload index).constraint
  linkedHint : (link_Main_reload index).hints = [reloadHint index]
  piop : (reloadHint index).piop = "Permutation"
  bus : (reloadHint index).busId = .constant "10"
  proves : (reloadHint index).proves = true
  multiplicity : (reloadHint index).multiplicity = .constant "1"
  exactNamedSlots : (reloadHint index).slots = expectedReloadSlots index
  slotInterpretation :
    reloadSlotsToClean rows index (reloadHint index).slots =
      some (reloadTuple
        (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr (reloadRowAt rows index)))

set_option maxRecDepth 10000 in
def reloadWiring (rows : ReloadRows) (index : Fin 31) : ReloadWiring rows index where
  linkShape := by fin_cases index <;> rfl
  constraintValidated := ValidatedLink.constraintValidated (link_Main_reload index)
  linkedHint := by fin_cases index <;> rfl
  piop := by fin_cases index <;> rfl
  bus := by fin_cases index <;> rfl
  proves := by fin_cases index <;> rfl
  multiplicity := by fin_cases index <;> rfl
  exactNamedSlots := by fin_cases index <;> rfl
  slotInterpretation := by
    rw [show (reloadHint index).slots = expectedReloadSlots index by
      fin_cases index <;> rfl]
    fin_cases index <;> rfl

end ZiskFv.AirsClean.Main
