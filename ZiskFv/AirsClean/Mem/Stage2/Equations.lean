import Extraction.LookupWiring

/-!
Source-only AST pins for Mem c24–c32; c33 is deliberately not part of this module.

Sources: immutable Mem source
`/nix/store/ma4jf8qlafpzsiv644h0jxz3pkw69d7w-source/state-machines/mem/pil/mem.pil`,
lines 195–203, 232–241, 263–286, 384–397, 435–440; pil2-proofman
ff0e33a9b40f2467b35ef26aa2aabb4a624dfed3,
`pil2-components/lib/std/pil/std_sum.pil` 571–590, 599, 640–656.
The emitted source citations are Extraction/Mem.lean 190–241.

Exact cell/type roster (all unmarked row offsets are zero):
* Phase-1 scalar witness stage 1: addr=0, step=1, sel=2,
  addr_changes=3, step_dual=4, sel_dual=5, value[0..1]=6..7,
  wr=8, previous_step=9, l_increment=10, h_increment=11,
  read_same_addr=12. Only 0,1,2,4,5,6,7,8,10,11 occur below.
* Scalar fixed stage 0: SEGMENT_L1=0 (unused here), __L1__=1.
* Phase-1 scalar air values: segment_id=0, is_first_segment=1 (unused),
  is_last_segment=2, previous_segment_value[0..1]=3..4,
  previous_segment_step=5, previous_segment_addr=6,
  segment_last_value[0..1]=7..8, segment_last_step=9,
  segment_last_addr=10, distance_base[0..1]=11..12,
  distance_end[0..1]=13..14.
* Stage-2 Ext3 witness: gsum=0, im_cluster[0]=1, im_cluster[1]=2.
  gsum alone also occurs at offset -1 in c26; __L1__ is CURRENT row.
* Stage-2 Ext3 air values: im_direct[0..5]=15..20.
* Stage-2 Ext3 challenges: alpha=index 0, gamma=index 1.

Bus IDs are 102 (24-bit range), 103 (16-bit range), 104 (22-bit
range), 10 (memory permutation), 11 (memory continuation). Memory
width is 8 and the continuation base byte address is 2684354560.
These are source constants, not arbitrary coefficients. The cluster
negative-one literal is retained as the exact source string p-1,
18446744069414584320, rather than rewriting it to a negation node.

These definitions only describe syntax: scalar cells must be embedded
when interpreted in Ext3, whose multiplication is cubic, with no Field
instance required. No source-validity premise, native binding, live/root
execution claim, denominator nonzero claim, or logUp closure is asserted.
-/
namespace ZiskFv.AirsClean.Mem.Stage2

open Extraction.LookupWiring (Expr)

/-- Source alpha and gamma, including their challenge stage. -/
def sourceAlpha : Expr := .challenge 2 0
def sourceGamma : Expr := .challenge 2 1

/-- One explicitly ordered source Horner step, not a generated slot fold. -/
def sourceHornerStep (high low : Expr) : Expr :=
  .add (.mul high sourceAlpha) low

/-- Source 16-bit range denominator for h_increment. -/
def highIncrementDenominator : Expr :=
  .add (sourceHornerStep (.witness 1 11 0) (.constant "103")) sourceGamma

/-- Source selected 24-bit range denominator for step_dual-step-wr. -/
def dualStepDenominator : Expr :=
  .add (sourceHornerStep
    (.sub (.sub (.witness 1 4 0) (.witness 1 1 0)) (.witness 1 8 0))
    (.constant "102")) sourceGamma

/-- Source primary permutation, in reverse-tuple Horner order. -/
def primaryMemoryDenominator : Expr :=
  .add (sourceHornerStep
    (sourceHornerStep
      (sourceHornerStep
        (sourceHornerStep
          (sourceHornerStep
            (sourceHornerStep (.witness 1 7 0) (.witness 1 6 0))
            (.constant "8"))
          (.witness 1 1 0))
        (.mul (.witness 1 0 0) (.constant "8")))
      (.add (.witness 1 8 0) (.constant "1")))
    (.constant "10")) sourceGamma

/-- Source dual permutation: READ=1, with the dual step. -/
def dualMemoryDenominator : Expr :=
  .add (sourceHornerStep
    (sourceHornerStep
      (sourceHornerStep
        (sourceHornerStep
          (sourceHornerStep
            (sourceHornerStep (.witness 1 7 0) (.witness 1 6 0))
            (.constant "8"))
          (.witness 1 4 0))
        (.mul (.witness 1 0 0) (.constant "8")))
      (.constant "1"))
    (.constant "10")) sourceGamma

/-- std_sum:590: two assumes, multiplicities -1 and -sel_dual. -/
def expected24 : Expr :=
  .sub (.mul (.witness 2 1 0) (.mul highIncrementDenominator dualStepDenominator))
    (.add (.mul (.constant "18446744069414584320") dualStepDenominator)
      (.mul (.sub (.constant "0") (.witness 1 5 0)) highIncrementDenominator))

/-- std_sum:590: two proves, multiplicities sel and sel_dual. -/
def expected25 : Expr :=
  .sub (.mul (.witness 2 2 0) (.mul primaryMemoryDenominator dualMemoryDenominator))
    (.add (.mul (.witness 1 2 0) dualMemoryDenominator)
      (.mul (.witness 1 5 0) primaryMemoryDenominator))

/-- std_sum:599: remaining 22-bit range assumes has numerator -1. -/
def expected26 : Expr :=
  .add (.mul
    (.sub (.sub (.witness 2 0 0)
      (.mul (.witness 2 0 (-1)) (.sub (.constant "1") (.fixed 1 0))))
      (.add (.witness 2 1 0) (.witness 2 2 0)))
    (.add (sourceHornerStep (.witness 1 10 0) (.constant "104")) sourceGamma))
    (.constant "1")

/-- Continuation assumes: previous value high/low, step, address, segment, base, bus. -/
def previousContinuationDenominator : Expr :=
  .add (sourceHornerStep
    (sourceHornerStep
      (sourceHornerStep
        (sourceHornerStep
          (sourceHornerStep
            (sourceHornerStep (.airValue 4) (.airValue 3)) (.airValue 5))
          (.airValue 6))
        (.airValue 0))
      (.constant "2684354560"))
    (.constant "11")) sourceGamma

/-- Continuation proves: last value high/low, step, address, NEXT segment, base, bus. -/
def nextContinuationDenominator : Expr :=
  .add (sourceHornerStep
    (sourceHornerStep
      (sourceHornerStep
        (sourceHornerStep
          (sourceHornerStep
            (sourceHornerStep (.airValue 8) (.airValue 7)) (.airValue 9))
          (.airValue 10))
        (.add (.airValue 0) (.constant "1")))
      (.constant "2684354560"))
    (.constant "11")) sourceGamma

/-- std_sum:656: direct[0] assumes with multiplicity -1. -/
def expected27 : Expr :=
  .add (.mul (.airValue 15) previousContinuationDenominator) (.constant "1")

/-- std_sum:656: direct[1] proves with multiplicity 1-is_last_segment. -/
def expected28 : Expr :=
  .sub (.mul (.airValue 16) nextContinuationDenominator)
    (.sub (.constant "1") (.airValue 2))

/-- distance_base[0], assumes, multiplicity -1. -/
def expected29 : Expr :=
  .add (.mul (.airValue 17)
    (.add (sourceHornerStep (.airValue 11) (.constant "103")) sourceGamma))
    (.constant "1")

/-- distance_base[1], assumes, multiplicity -1. -/
def expected30 : Expr :=
  .add (.mul (.airValue 18)
    (.add (sourceHornerStep (.airValue 12) (.constant "103")) sourceGamma))
    (.constant "1")

/-- distance_end[0], assumes, multiplicity -1. -/
def expected31 : Expr :=
  .add (.mul (.airValue 19)
    (.add (sourceHornerStep (.airValue 13) (.constant "103")) sourceGamma))
    (.constant "1")

/-- distance_end[1], assumes, multiplicity -1. -/
def expected32 : Expr :=
  .add (.mul (.airValue 20)
    (.add (sourceHornerStep (.airValue 14) (.constant "103")) sourceGamma))
    (.constant "1")

theorem actual24_eq_expected24 : Extraction.LookupWiring.constraint_Mem_24 = expected24 := by rfl
theorem actual25_eq_expected25 : Extraction.LookupWiring.constraint_Mem_25 = expected25 := by rfl
theorem actual26_eq_expected26 : Extraction.LookupWiring.constraint_Mem_26 = expected26 := by rfl
theorem actual27_eq_expected27 : Extraction.LookupWiring.constraint_Mem_27 = expected27 := by rfl
theorem actual28_eq_expected28 : Extraction.LookupWiring.constraint_Mem_28 = expected28 := by rfl
theorem actual29_eq_expected29 : Extraction.LookupWiring.constraint_Mem_29 = expected29 := by rfl
theorem actual30_eq_expected30 : Extraction.LookupWiring.constraint_Mem_30 = expected30 := by rfl
theorem actual31_eq_expected31 : Extraction.LookupWiring.constraint_Mem_31 = expected31 := by rfl
theorem actual32_eq_expected32 : Extraction.LookupWiring.constraint_Mem_32 = expected32 := by rfl

/-- Exactly c24–c32, not the frozen c33 finalizer. -/
def actualNonlinear (i : Fin 9) : Expr :=
  match i.val with
  | 0 => Extraction.LookupWiring.constraint_Mem_24
  | 1 => Extraction.LookupWiring.constraint_Mem_25
  | 2 => Extraction.LookupWiring.constraint_Mem_26
  | 3 => Extraction.LookupWiring.constraint_Mem_27
  | 4 => Extraction.LookupWiring.constraint_Mem_28
  | 5 => Extraction.LookupWiring.constraint_Mem_29
  | 6 => Extraction.LookupWiring.constraint_Mem_30
  | 7 => Extraction.LookupWiring.constraint_Mem_31
  | _ => Extraction.LookupWiring.constraint_Mem_32

def expectedNonlinear (i : Fin 9) : Expr :=
  match i.val with
  | 0 => expected24
  | 1 => expected25
  | 2 => expected26
  | 3 => expected27
  | 4 => expected28
  | 5 => expected29
  | 6 => expected30
  | 7 => expected31
  | _ => expected32

theorem actualNonlinear_eq_expectedNonlinear (i : Fin 9) :
    actualNonlinear i = expectedNonlinear i := by
  fin_cases i <;> rfl

end ZiskFv.AirsClean.Mem.Stage2
