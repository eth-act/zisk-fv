import Extraction.Arith
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

/-- Source-shaped value of the c61 `bus_res0` slot.  Keeping this small raw
expression pin separate from the semantic slot translation makes mutations
of either 16-bit limb fail before Lean attempts the larger translation. -/
def arithBusRes0Expr : Expr :=
  .add
    (.add
      (.add
        (.mul
          (.sub (.sub (.constant "1") (.witness 1 34 0)) (.witness 1 33 0))
          (.add (.witness 1 19 0) (.mul (.witness 1 20 0) (.constant "65536"))))
        (.mul
          (.witness 1 34 0)
          (.add (.witness 1 15 0) (.mul (.witness 1 16 0) (.constant "65536")))))
      (.mul
        (.witness 1 33 0)
        (.add (.witness 1 7 0) (.mul (.witness 1 8 0) (.constant "65536")))))
    (.constant "0")

/-- The c61 result slot is pinned directly to the extracted syntax.  Rounds
38 and 46 exchange one pair of limbs in this slot. -/
theorem arithBusRes0SlotPinned :
    hint_Arith_61_0.slots[5]? =
      some { name := "bus_res0", value := arithBusRes0Expr } := by
  rfl

/-- All generated links whose hints consume the Arith range channel.

c52 also contains the existing bus-331 Arith-table lookup.  c61 is the
operation-bus link already bound by `operationWiring`; c62 is the direct
global-sum recurrence; c64 is the final-row link. -/
def arithRangeLinks : List ValidatedLink :=
  [ link_Arith_49, link_Arith_50, link_Arith_51, link_Arith_52
  , link_Arith_53, link_Arith_54, link_Arith_55, link_Arith_56
  , link_Arith_57, link_Arith_58, link_Arith_59, link_Arith_60
  , link_Arith_63 ]

theorem arithRangeLinks_length : arithRangeLinks.length = 13 := by
  rfl

/-- The sole c62 constraint has no hint payload; retain the generated
declaration directly rather than inventing a channel message for it. -/
abbrev arithConstraint62EveryRow {C : Type → Type → Sort u} {F : Type}
    [Field F] [Extraction.Circuit F F C] (c : C F F) (row : ℕ) :=
  Arith.extraction.constraint_62_every_row c row

/-- c64 is the generated final-row closure for the same global sum. -/
def arithFinalRowLink : ValidatedFinalRow := link_Arith_64

theorem arithFinalRowLink_is_c64 : arithFinalRowLink = link_Arith_64 := by
  rfl

end ZiskFv.AirsClean.ArithMul
