import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.Data
import ZiskFv.AirsClean.Mem.Stage2.Equations
import ZiskFv.AirsClean.Mem.Stage2.Literals
import ZiskFv.AirsClean.Mem.SourceFinalizerEquation
import ZiskFv.AirsClean.MemMirrorWeld

/-! Correspondence of the independently stated chosen-image equations to the
actual generated Mem projections. The fifteen mixed clauses use the extractor's
typed records, c24–c32 use its nonlinear expressions, and c33 retains the distinct
AIR-GROUP leaf. The nine local clauses use the existing generated-predicate weld,
not an invented typed AST. None of these results assumes native-cell recovery.

Sources: b632 mem.pil103–175,195–241,263–286,365–397,403–440;
proofman ff0e33a9 std_sum.pil571–599,640–696. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open Stage2

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- The exact fifteen actual typed mixed-clause records, in generated order. -/
def mixedSource (equation : Fin 15) : ConstraintOnly :=
  match equation.val with
  | 0 => constraintOnly_Mem_0
  | 1 => constraintOnly_Mem_1
  | 2 => constraintOnly_Mem_2
  | 3 => constraintOnly_Mem_9
  | 4 => constraintOnly_Mem_10
  | 5 => constraintOnly_Mem_11
  | 6 => constraintOnly_Mem_12
  | 7 => constraintOnly_Mem_13
  | 8 => constraintOnly_Mem_14
  | 9 => constraintOnly_Mem_15
  | 10 => constraintOnly_Mem_16
  | 11 => constraintOnly_Mem_17
  | 12 => constraintOnly_Mem_19
  | 13 => constraintOnly_Mem_20
  | _ => constraintOnly_Mem_22

/-- Positions in the independently stated twenty-four segment residuals. -/
def mixedIndex (equation : Fin 15) : Fin 24 :=
  match equation.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 9
  | 4 => 10
  | 5 => 11
  | 6 => 12
  | 7 => 13
  | 8 => 14
  | 9 => 15
  | 10 => 16
  | 11 => 17
  | 12 => 19
  | 13 => 20
  | _ => 22

theorem mixed_source_index (equation : Fin 15) :
    (mixedSource equation).air = "Mem" ∧
      (mixedSource equation).constraintIndex = (mixedIndex equation).val := by
  fin_cases equation <;> exact ⟨rfl, rfl⟩

private theorem nat_previous_address : "335544320".toNat? = some 335544320 := by
  change (String.ofList ['3', '3', '5', '5', '4', '4', '3', '2', '0']).toNat? = some 335544320
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    MemAlignWriteByte.SourceLiterals.foldl_ofList]
  simp [String.Slice.isEmpty]

private theorem nat_distance_radix : "65536".toNat? = some 65536 := by
  change (String.ofList ['6', '5', '5', '3', '6']).toNat? = some 65536
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    MemAlignWriteByte.SourceLiterals.foldl_ofList]
  simp [String.Slice.isEmpty]

private theorem nat_last_address : "402653183".toNat? = some 402653183 := by
  change (String.ofList ['4', '0', '2', '6', '5', '3', '1', '8', '3']).toNat? = some 402653183
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    MemAlignWriteByte.SourceLiterals.foldl_ofList]
  simp [String.Slice.isEmpty]

private theorem nat_increment_radix : "4194304".toNat? = some 4194304 := by
  change (String.ofList ['4', '1', '9', '4', '3', '0', '4']).toNat? = some 4194304
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    MemAlignWriteByte.SourceLiterals.foldl_ofList]
  simp [String.Slice.isEmpty]

@[simp] private theorem literal_previous_address :
    literal? "335544320" = some (Ext3.ofBase (335544320 : FGL)) := by
  simp [literal?, nat_previous_address]

@[simp] private theorem literal_distance_radix :
    literal? "65536" = some (Ext3.ofBase (65536 : FGL)) := by
  simp [literal?, nat_distance_radix]

@[simp] private theorem literal_last_address :
    literal? "402653183" = some (Ext3.ofBase (402653183 : FGL)) := by
  simp [literal?, nat_last_address]

@[simp] private theorem literal_increment_radix :
    literal? "4194304" = some (Ext3.ofBase (4194304 : FGL)) := by
  simp [literal?, nat_increment_radix]

/-- All fifteen typed mixed clauses, with the actual source kinds, signed
rotations and operand order interpreted on the closed chosen data. -/
theorem mixed_source_correspondence (view : View resolved) (row : Index)
    (equation : Fin 15) :
    polynomial view row (mixedSource equation).constraint =
      some (Ext3.ofBase (segmentResidual view row (mixedIndex equation))) := by
  fin_cases equation <;>
    simp [mixedSource, mixedIndex, constraintOnly_Mem_0, constraintOnly_Mem_1,
      constraintOnly_Mem_2, constraintOnly_Mem_9, constraintOnly_Mem_10,
      constraintOnly_Mem_11, constraintOnly_Mem_12, constraintOnly_Mem_13,
      constraintOnly_Mem_14, constraintOnly_Mem_15, constraintOnly_Mem_16,
      constraintOnly_Mem_17, constraintOnly_Mem_19, constraintOnly_Mem_20,
      constraintOnly_Mem_22, polynomial, witnessCell, airCell, fixedCell,
      segmentResidual, primary, baseAir, View.previous,
      ← Ext3.ofBase_add, ← Ext3.ofBase_sub, ← Ext3.ofBase_mul,
      ← Ext3.ofBase_neg, ← Ext3.ofBase_zero, ← Ext3.ofBase_one]
  all_goals
    first | rfl | (apply congrArg Ext3.ofBase; ring)

/-- Actual c24–c32 against the independent local polynomial row. No generated
expression is used to define either the leaf data or the target residuals. -/
theorem nonlinear_source_correspondence (view : View resolved) (row : Index)
    (equation : Fin 9) :
    polynomial view row (actualNonlinear equation) =
      some ((polynomialRow view row).residual equation) := by
  rw [actualNonlinear_eq_expectedNonlinear]
  fin_cases equation <;>
    simp [expectedNonlinear, expected24, expected25, expected26, expected27,
      expected28, expected29, expected30, expected31, expected32,
      sourceAlpha, sourceGamma, sourceHornerStep, highIncrementDenominator,
      dualStepDenominator, primaryMemoryDenominator, dualMemoryDenominator,
      previousContinuationDenominator, nextContinuationDenominator,
      polynomial, witnessCell, airCell, fixedCell, challengeCell, alpha, gamma,
      extensionWitness, primary, baseAir, polynomialRow, View.previous,
      PolynomialRow.residual, PolynomialRow.residual24, PolynomialRow.residual25,
      PolynomialRow.residual26, PolynomialRow.residual27, PolynomialRow.residual28,
      PolynomialRow.residual29, PolynomialRow.residual30, PolynomialRow.residual31,
      PolynomialRow.residual32, PolynomialRow.highDen, PolynomialRow.dualStepDen,
      PolynomialRow.lowDen, PolynomialRow.primaryDen, PolynomialRow.dualDen,
      PolynomialRow.previousDen, PolynomialRow.nextDen,
      ← Ext3.ofBase_add, ← Ext3.ofBase_sub, ← Ext3.ofBase_mul,
      ← Ext3.ofBase_neg, ← Ext3.ofBase_zero, ← Ext3.ofBase_one]
  all_goals
    first | rfl | (apply congrArg Ext3.ofBase; ring)

/-- Source c33 reads GROUP0, not the legacy scalar exposed AIR0. Both signs,
the next physical-row selector and all six direct terms remain in source order. -/
theorem finalizer_source_correspondence (view : View resolved) (row : Index) :
    polynomial view row constraint_Mem_33 =
      some ((polynomialRow view row).residual33) := by
  rw [SourceFinalizer.compiled_constraint_eq_expected]
  simp [SourceFinalizer.expectedConstraint, polynomial, witnessCell, airCell,
    fixedCell, groupCell, extensionWitness, polynomialRow,
    PolynomialRow.residual33, PolynomialRow.directSum]

/-- Exact existing Spec ↔ actual nine local generated projections. These
predicates have no typed Expr record; this theorem deliberately uses the weld. -/
theorem local_generated_correspondence (row : Index) :
    Spec (primaryRow row) ↔
      Mem.extraction.constraint_3_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_4_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_5_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_6_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_7_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_8_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_18_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_21_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 ∧
      Mem.extraction.constraint_23_every_row
        (MemMirrorWeld.extractedMemRow (primaryRow row)) 0 :=
  MemMirrorWeld.spec_weld (primaryRow row)

/-- The other nine independently stated segment residuals are exactly the
local Spec just welded above; no clause of c0–c23 is left outside the binding. -/
theorem local_segment_correspondence (view : View resolved) (row : Index) :
    (segmentResidual view row 3 = 0 ∧
      segmentResidual view row 4 = 0 ∧
      segmentResidual view row 5 = 0 ∧
      segmentResidual view row 6 = 0 ∧
      segmentResidual view row 7 = 0 ∧
      segmentResidual view row 8 = 0 ∧
      segmentResidual view row 18 = 0 ∧
      segmentResidual view row 21 = 0 ∧
      segmentResidual view row 23 = 0) ↔ Spec (primaryRow row) := by
  rfl

/-- Closed-data interpretation fails closed on unsupported generated syntax. -/
theorem polynomial_opaque (view : View resolved) (row : Index) (tag payload : String) :
    polynomial view row (.opaque tag payload) = none := rfl

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness
