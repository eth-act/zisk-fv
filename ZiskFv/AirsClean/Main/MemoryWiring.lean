import Extraction.LookupWiring
import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.Main.Wiring

/-!
# Main per-row memory-bus wiring

This module binds the six physical Main memory interactions to the six messages
emitted by `mainWithRomMemAndOpBus`. It deliberately excludes the separate 31
end-of-segment register-flush producers (Main c50, c53, ..., c140).
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusMessage)

@[reducible]
def memTuple (message : MemBusMessage (Expression FGL)) : List (Expression FGL) :=
  [message.mem_op, message.ptr, message.timestamp, message.width,
    message.value_0, message.value_1]

/-- One exact physical memory hint together with the validated constraint link
that owns it. `allHints` retains non-memory siblings in clustered links. -/
structure MemoryHintBinding (row : Var MainRowWithRom FGL) where
  link : ValidatedLink
  hint : HintTuple
  allHints : List HintTuple
  shape : LinkShape
  sourceProves : Bool
  sourceMultiplicity : Expression FGL
  sourceMessage : MemBusMessage (Expression FGL)
  linkedHints : link.hints = allHints
  linkShape : link.shape = shape
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  hintInLink : hint ∈ allHints
  piop : hint.piop = "Permutation"
  bus : hint.busId = .constant "10"
  direction : hint.proves = sourceProves
  multiplicityInterpretation :
    operationExprToClean row hint.multiplicity = some sourceMultiplicity
  slotInterpretation : operationSlotsToClean row hint.slots =
    some (memTuple sourceMessage)

/-- Exact a-side current-access tuple from Main c39. The source uses
`a_offset_imm0` and `1 + 4 * STEP`; their relation to the component's `addr0`
and timestamp spelling is proved semantically below. -/
@[reducible]
def sourceAMemMessageExpr (row : Var MainRowWithRom FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := row.rom.a_src_mem + 3 * row.rom.a_src_reg
    ptr := row.rom.a_offset_imm0
    timestamp := 1 + 4 * row.rom.main_step
    width := 8
    value_0 := row.core.a_0
    value_1 := row.core.a_1 }

/-- Exact b-side current-access tuple from Main c43. -/
@[reducible]
def sourceBMemMessageExpr (row : Var MainRowWithRom FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := (row.rom.b_src_mem + row.rom.b_src_ind) + 3 * row.rom.b_src_reg
    ptr := row.rom.addr1
    timestamp := (1 + 4 * row.rom.main_step) + 1
    width := row.rom.b_src_ind * (row.core.ind_width - 8) + 8
    value_0 := row.core.b_0
    value_1 := row.core.b_1 }

/-- Exact c-side current/store tuple from Main c44. The source constructs the
address inline as `store_offset + store_ind * a[0]`. -/
@[reducible]
def sourceCMemMessageExpr (row : Var MainRowWithRom FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := 2 * (row.rom.store_mem + row.rom.store_ind) + 3 * row.rom.store_reg
    ptr := row.rom.store_offset + row.rom.store_ind * row.core.a_0
    timestamp := (1 + 4 * row.rom.main_step) + 2
    width := row.rom.store_ind * (row.core.ind_width - 8) + 8
    value_0 := row.core.store_pc *
        (row.core.pc + row.core.jmp_offset2 - row.core.c_0) + row.core.c_0
    value_1 := (1 - row.core.store_pc) * row.core.c_1 }

set_option maxRecDepth 10000 in
@[reducible]
def aCurrentMemoryWiring (row : Var MainRowWithRom FGL) : MemoryHintBinding row where
  link := link_Main_39
  hint := hint_Main_39_0
  allHints := [hint_Main_39_0, hint_Main_39_1]
  shape := .cluster2
  sourceProves := false
  sourceMultiplicity := row.rom.a_src_mem + row.rom.a_src_reg
  sourceMessage := sourceAMemMessageExpr row
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_39
  hintInLink := by simp
  piop := rfl
  bus := rfl
  direction := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

set_option maxRecDepth 10000 in
@[reducible]
def bPreviousMemoryWiring (row : Var MainRowWithRom FGL) : MemoryHintBinding row where
  link := link_Main_39
  hint := hint_Main_39_1
  allHints := [hint_Main_39_0, hint_Main_39_1]
  shape := .cluster2
  sourceProves := true
  sourceMultiplicity := row.rom.b_src_reg
  sourceMessage := bRegPreMessageExpr row
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_39
  hintInLink := by simp
  piop := rfl
  bus := rfl
  direction := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

set_option maxRecDepth 10000 in
@[reducible]
def cPreviousMemoryWiring (row : Var MainRowWithRom FGL) : MemoryHintBinding row where
  link := link_Main_40
  hint := hint_Main_40_0
  allHints := [hint_Main_40_0, hint_Main_40_1]
  shape := .cluster2
  sourceProves := true
  sourceMultiplicity := row.rom.store_reg
  sourceMessage := cRegPreMessageExpr row
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_40
  hintInLink := by simp
  piop := rfl
  bus := rfl
  direction := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

set_option maxRecDepth 10000 in
@[reducible]
def bCurrentMemoryWiring (row : Var MainRowWithRom FGL) : MemoryHintBinding row where
  link := link_Main_43
  hint := hint_Main_43_0
  allHints := [hint_Main_43_0]
  shape := .directAssumesNegForm
  sourceProves := false
  sourceMultiplicity := row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg
  sourceMessage := sourceBMemMessageExpr row
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_43
  hintInLink := by simp
  piop := rfl
  bus := rfl
  direction := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

set_option maxRecDepth 10000 in
@[reducible]
def cCurrentMemoryWiring (row : Var MainRowWithRom FGL) : MemoryHintBinding row where
  link := link_Main_44
  hint := hint_Main_44_0
  allHints := [hint_Main_44_0]
  shape := .directAssumesNegForm
  sourceProves := false
  sourceMultiplicity := row.rom.store_mem + row.rom.store_ind + row.rom.store_reg
  sourceMessage := sourceCMemMessageExpr row
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_44
  hintInLink := by simp
  piop := rfl
  bus := rfl
  direction := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

set_option maxRecDepth 10000 in
@[reducible]
def aPreviousMemoryWiring (row : Var MainRowWithRom FGL) : MemoryHintBinding row where
  link := link_Main_46
  hint := hint_Main_46_0
  allHints := [hint_Main_46_0]
  shape := .direct
  sourceProves := true
  sourceMultiplicity := row.rom.a_src_reg
  sourceMessage := aRegPreMessageExpr row
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_46
  hintInLink := by simp
  piop := rfl
  bus := rfl
  direction := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

/-- Exhaustive finite roster of the live component's six per-row memory
messages, in the same a-prev/a-current/b-prev/b-current/c-prev/c-current order
used by `mainWithRomMemAndOpBus`. -/
@[reducible]
def perRowMemoryRoster (row : Var MainRowWithRom FGL) :
    List (MemoryHintBinding row) :=
  [aPreviousMemoryWiring row, aCurrentMemoryWiring row,
    bPreviousMemoryWiring row, bCurrentMemoryWiring row,
    cPreviousMemoryWiring row, cCurrentMemoryWiring row]

theorem perRowMemoryRoster_length (row : Var MainRowWithRom FGL) :
    (perRowMemoryRoster row).length = 6 := by
  rfl

/-- Convert the source-side direction bit to Clean's signed emission
multiplicity: producer hints are positive and consumer hints are negative. -/
@[reducible]
def signedMultiplicity {row : Var MainRowWithRom FGL}
    (binding : MemoryHintBinding row) : Expression FGL :=
  if binding.sourceProves = true then binding.sourceMultiplicity
  else -binding.sourceMultiplicity

/-- The finite roster has exactly the six signed multiplicities emitted by
`mainWithRomMemAndOpBus`, in its exposed interaction order. -/
theorem perRowMemoryRoster_signedMultiplicities (row : Var MainRowWithRom FGL) :
    (perRowMemoryRoster row).map signedMultiplicity =
      [row.rom.a_src_reg,
        -(row.rom.a_src_mem + row.rom.a_src_reg),
        row.rom.b_src_reg,
        -(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg),
        row.rom.store_reg,
        -(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg)] := by
  rfl

@[reducible]
def sourcePerRowMemoryMessages (row : Var MainRowWithRom FGL) :
    List (MemBusMessage (Expression FGL)) :=
  (perRowMemoryRoster row).map MemoryHintBinding.sourceMessage

@[reducible]
def livePerRowMemoryMessages (row : Var MainRowWithRom FGL) :
    List (MemBusMessage (Expression FGL)) :=
  [aRegPreMessageExpr row, aMemMessageExpr row,
    bRegPreMessageExpr row, bMemMessageExpr row,
    cRegPreMessageExpr row, cMemMessageExpr row]

theorem eval_sourceAMemMessageExpr_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL)
    (h_ptr : Expression.eval env row.rom.addr0 =
      Expression.eval env row.rom.a_offset_imm0) :
    eval env (sourceAMemMessageExpr row) = eval env (aMemMessageExpr row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [sourceAMemMessageExpr, aMemMessageExpr, aMemOpExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat' apply And.intro
  all_goals try trivial
  all_goals first | exact h_ptr.symm | ring

theorem eval_sourceBMemMessageExpr_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    eval env (sourceBMemMessageExpr row) = eval env (bMemMessageExpr row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [sourceBMemMessageExpr, bMemMessageExpr, bMemOpExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat' apply And.intro
  all_goals try trivial
  all_goals ring

theorem eval_sourceCMemMessageExpr_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL)
    (h_ptr : Expression.eval env row.rom.addr2 =
      Expression.eval env
        (row.rom.store_offset + row.rom.store_ind * row.core.a_0)) :
    eval env (sourceCMemMessageExpr row) = eval env (cMemMessageExpr row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [sourceCMemMessageExpr, cMemMessageExpr, cMemOpExpr,
    storeValueLoExpr, storeValueHiExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat' apply And.intro
  all_goals try trivial
  all_goals first | exact h_ptr.symm | ring

/-- Under Main's existing address-placement scope, the six exact physical
tuples evaluate to the six live component messages. -/
theorem eval_sourcePerRowMemoryMessages_eq_live (env : Environment FGL)
    (row : Var MainRowWithRom FGL)
    (h_address : AddressSpec (eval env row)) :
    (sourcePerRowMemoryMessages row).map (eval env) =
      (livePerRowMemoryMessages row).map (eval env) := by
  have h_addr0 : Expression.eval env row.rom.addr0 =
      Expression.eval env row.rom.a_offset_imm0 := by
    simpa only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field] using h_address.1
  have h_addr2 : Expression.eval env row.rom.addr2 =
      Expression.eval env
        (row.rom.store_offset + row.rom.store_ind * row.core.a_0) := by
    simpa only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field, Expression.eval] using h_address.2.2.1
  simp only [sourcePerRowMemoryMessages, perRowMemoryRoster,
    livePerRowMemoryMessages, List.map_cons, List.map_nil,
    aPreviousMemoryWiring, aCurrentMemoryWiring, bPreviousMemoryWiring,
    bCurrentMemoryWiring, cPreviousMemoryWiring, cCurrentMemoryWiring]
  rw [eval_sourceAMemMessageExpr_eq_live env row h_addr0,
    eval_sourceBMemMessageExpr_eq_live env row,
    eval_sourceCMemMessageExpr_eq_live env row h_addr2]

theorem componentPerRowMemoryMessages_eq_live
    (length : Nat) (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold env) :
    (sourcePerRowMemoryMessages
        (componentWithRomMemAndOpBus length program).rowInputVar).map (eval env) =
      (livePerRowMemoryMessages
        (componentWithRomMemAndOpBus length program).rowInputVar).map (eval env) := by
  apply eval_sourcePerRowMemoryMessages_eq_live
  exact addressSpec_of_componentWithRomMemAndOpBus_constraints
    length program env h_holds

end ZiskFv.AirsClean.Main
