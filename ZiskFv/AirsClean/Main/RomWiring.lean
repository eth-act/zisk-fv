import Extraction.LookupWiring
import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.Main.Wiring

/-!
# Main instruction-ROM wiring

The generated c42 link is Main's assume-side bus-7890 lookup. This module
interprets its physical source tuple as the exact `romMessageExpr` consumed by
the live Main component, including source order, PC, and packed ROM flags.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program romStaticTable)

@[reducible]
def romTuple (message : ZiskRomMessage (Expression FGL)) : List (Expression FGL) :=
  [message.line, message.a_offset_imm0, message.a_imm1,
    message.b_offset_imm0, message.b_imm1, message.ind_width, message.op,
    message.store_offset, message.jmp_offset1, message.jmp_offset2, message.flags]

/-- The exact extraction facts carried by Main c42. -/
structure RomWiring (row : Var MainRowWithRom FGL) where
  link : ValidatedLink
  romHint : HintTuple
  c42Link : link = link_Main_42
  linkedHints : link.hints = [romHint]
  linkShape : link.shape = .direct
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  romPiop : romHint.piop = "Lookup"
  romBus : romHint.busId = .constant "7890"
  romIsAssumes : romHint.proves = false
  romMultiplicity : romHint.multiplicity = .constant "1"
  multiplicityInterpretation : operationExprToClean row romHint.multiplicity = some 1
  slotInterpretation : operationSlotsToClean row romHint.slots =
    some (romTuple (romMessageExpr row))

set_option maxRecDepth 10000 in
@[reducible]
def romWiring (row : Var MainRowWithRom FGL) : RomWiring row where
  link := link_Main_42
  romHint := hint_Main_42_0
  c42Link := rfl
  linkedHints := rfl
  linkShape := rfl
  constraintValidated := ValidatedLink.constraintValidated link_Main_42
  romPiop := rfl
  romBus := rfl
  romIsAssumes := rfl
  romMultiplicity := rfl
  multiplicityInterpretation := rfl
  slotInterpretation := rfl

/-- Evaluation of the interpreted physical slots is evaluation of the live
typed ROM entry, with no supplied representation equality. -/
theorem romWiring_evaluatedEntry (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    (operationSlotsToClean row (romWiring row).romHint.slots).map
        (List.map (Expression.eval env)) =
      some (List.map (Expression.eval env) (romTuple (romMessageExpr row))) := by
  rw [(romWiring row).slotInterpretation]
  rfl

/-- The c42 tuple specializes directly to the actual ROM entry expressions of
the unified live Main component. -/
theorem componentRomWiring_slotInterpretation
    (length : Nat) (program : Program length) :
    operationSlotsToClean
        (componentWithRomMemAndOpBus length program).rowInputVar
        (romWiring
          (componentWithRomMemAndOpBus length program).rowInputVar).romHint.slots =
      some
        (romTuple
          (romMessageExpr
            (componentWithRomMemAndOpBus length program).rowInputVar)) := by
  exact
    (romWiring
      (componentWithRomMemAndOpBus length program).rowInputVar).slotInterpretation

/-- Actual component acceptance supplies program-ROM membership for the same
entry. No table-membership or table-validity premise is introduced here. -/
theorem componentRomWiring_lookupMember
    (length : Nat) (program : Program length) (env : Environment FGL)
    (h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold env) :
    (romStaticTable length program).Spec
      (eval env
        (romMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)) := by
  exact romSpec_of_componentWithRomMemAndOpBus_constraints length program env h_holds

end ZiskFv.AirsClean.Main
