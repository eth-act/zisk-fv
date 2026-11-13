import Extraction.LookupWiring
import ZiskFv.AirsClean.ArithMul.Wiring
import ZiskFv.AirsClean.ArithRangeSlice

/-!
# Arith range-channel extraction wiring

The physical `Arith` AIR is represented by the shared `ArithMulRow`; the
`ArithDivRow` is a proof-facing view of that same row, not a second PIL AIR.
This packet keeps the generated c49--c64 protocol objects reachable beside
the typed bus-330 provider.  It adds no caller premise: every link below
contains its own kernel-checked equality to the extracted constraint.
-/

namespace ZiskFv.AirsClean.ArithMul

open Extraction.LookupWiring
open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- All generated links whose hints consume the Arith range channel.

c52 also contains the existing bus-331 Arith-table lookup.  c61 is the
operation-bus link already bound by `operationWiring`; c62 is the live
remainder-bound comparison request tied below; c64 is the final-row link. -/
def arithRangeLinks : List ValidatedLink :=
  [ link_Arith_49, link_Arith_50, link_Arith_51, link_Arith_52
  , link_Arith_53, link_Arith_54, link_Arith_55, link_Arith_56
  , link_Arith_57, link_Arith_58, link_Arith_59, link_Arith_60
  , link_Arith_63 ]

theorem arithRangeLinks_length : arithRangeLinks.length = 13 := by
  rfl

/-- The c62 comparison request uses PIL's constant-first packing while the
live model uses limb-first packing. This normalization is field commutativity,
not a change to the requested tuple. -/
theorem remainder_pack_commutes (limb : FGL) : 65536 * limb = limb * 65536 := by
  exact mul_comm _ _

/-- All eleven c62 slots are tied to the actual remainder-bound consumer,
including signed/W-mode extension, comparison opcode, and trailing flags. -/
theorem remainderBound_slots_source :
    operationSlotsToClean hint_Arith_62_0.slots =
      some (opBusTuple (remainderBoundOpBusMessageExpr componentComplete.rowInputVar)) := by
  rfl

theorem remainderBound_multiplicity_source :
    operationExprToClean hint_Arith_62_0.multiplicity =
      some (componentComplete.rowInputVar.flags.div *
        (1 - componentComplete.rowInputVar.flags.div_by_zero)) := by
  rfl

/-- Keep the exact validated c62 link and its direction, bus, multiplicity,
and payload together. No surrogate message or new caller premise is used. -/
theorem remainderBound_link_source :
    link_Arith_62.hints = [hint_Arith_62_0] ∧
    hint_Arith_62_0.piop = "Lookup" ∧
    hint_Arith_62_0.proves = false ∧
    hint_Arith_62_0.busId = .constant "5000" ∧
    templateOf link_Arith_62.shape link_Arith_62.alpha link_Arith_62.gamma
      link_Arith_62.accumulator link_Arith_62.hints link_Arith_62.derivedTuples =
      some link_Arith_62.constraint := by
  exact ⟨rfl, rfl, rfl, rfl, link_Arith_62.constraintValidated⟩

/-- The source-tied request is the second interaction of the live completed
Arith component, with the required negative consumer multiplicity. -/
theorem remainderBound_live_interaction :
    (componentComplete.operations.interactionsWith OpBusChannel.toRaw)[1]? =
      some ((OpBusChannel.emitted
        (-(componentComplete.rowInputVar.flags.div *
          (1 - componentComplete.rowInputVar.flags.div_by_zero)))
        (remainderBoundOpBusMessageExpr componentComplete.rowInputVar)).toRaw) := by
  rw [componentComplete_interactionsWith_opBus]
  rfl

/-- c64 is the generated final-row closure for the same global sum. -/
def arithFinalRowLink : ValidatedFinalRow := link_Arith_64

theorem arithFinalRowLink_is_c64 : arithFinalRowLink = link_Arith_64 := by
  rfl

end ZiskFv.AirsClean.ArithMul
