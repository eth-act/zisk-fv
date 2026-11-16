import ZiskFv.AirsClean.Mem.PhysicalSource.PolynomialSource
import ZiskFv.AirsClean.Mem.PhysicalSource.DecodedView
import ZiskFv.AirsClean.Mem.SourceFinalizerEquation

/-! Structural decoding correspondence, not source producer authentication.
The raw physical model exists for EVERY CompleteView. Typed evaluator equality
additionally uses the privately computed DecodedView's actual ordered AIR/GROUP
profile checks. An arbitrary old CompleteView does not imply those checks:
erasing AIR/GROUP maps preserves its geometry/raw native buffers but makes the
metadata-driven typed AIR/GROUP reader return None. No such false implication,
caller Holds/coherence premise, r.id authentication or live Root claim is made.
-/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Stage2 Extraction.LookupWiring

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

namespace DecodedView

private theorem base_air_eq (view : DecodedView resolved) (column : Fin 15) :
    view.baseAir column = view.complete.baseAir column := rfl

private theorem base_air_source (view : DecodedView resolved) (column : Fin 15) :
    Stage2.airValue? resolved column.val =
      some (Ext3.ofBase (view.complete.baseAir column)) := by
  have bound : column.val < 21 := by have within := column.isLt; omega
  have actual := view.airValue_source ⟨column.val, bound⟩
  simpa [column.isLt, base_air_eq] using actual

private theorem direct_source (view : DecodedView resolved) (column : Fin 6) :
    Stage2.airValue? resolved (15 + column.val) =
      some (view.complete.direct column) := by
  have bound : 15 + column.val < 21 := by have within := column.isLt; omega
  have notBase : ¬15 + column.val < 15 := by omega
  have actual := view.airValue_source ⟨15 + column.val, bound⟩
  simpa [notBase] using actual

private theorem primary_source (view : DecodedView resolved) (row : view.complete.Index)
    (column : Fin 13) :
    Stage2.witness? resolved row.val 1 column.val 0 =
      some (Ext3.ofBase (view.complete.scalar row column)) := by
  simpa only [view.complete.base.rotate_zero] using
    Stage2.witness_stage1_source view.complete row column 0

/-- EVERY computed refined view, all nine actual source nonlinear equations.
No satisfiability hypothesis is transferred into the conclusion. -/
theorem nonlinear_polynomial_source (view : DecodedView resolved)
    (row : view.complete.Index) (equation : Fin 9) :
    Stage2.polynomial? resolved row.val (actualNonlinear equation) =
      some ((view.complete.polynomialRow row).residual equation) := by
  rw [actualNonlinear_eq_expectedNonlinear]
  fin_cases equation <;>
    simp [expectedNonlinear, expected24, expected25, expected26, expected27,
      expected28, expected29, expected30, expected31, expected32,
      sourceAlpha, sourceGamma, sourceHornerStep, highIncrementDenominator,
      dualStepDenominator, primaryMemoryDenominator, dualMemoryDenominator,
      previousContinuationDenominator, nextContinuationDenominator,
      Stage2.polynomial?,
      primary_source view row (0 : Fin 13), primary_source view row (1 : Fin 13),
      primary_source view row (2 : Fin 13), primary_source view row (4 : Fin 13),
      primary_source view row (5 : Fin 13), primary_source view row (6 : Fin 13),
      primary_source view row (7 : Fin 13), primary_source view row (8 : Fin 13),
      primary_source view row (10 : Fin 13), primary_source view row (11 : Fin 13),
      view.complete.auxiliary_source row (0 : Fin 3) 0,
      view.complete.auxiliary_source row (0 : Fin 3) (-1),
      view.complete.auxiliary_source row (1 : Fin 3) 0,
      view.complete.auxiliary_source row (2 : Fin 3) 0,
      view.complete.challenge_source (0 : Fin 2),
      view.complete.challenge_source (1 : Fin 2),
      view.complete.polynomial_l1_current row,
      base_air_source view (0 : Fin 15), base_air_source view (2 : Fin 15),
      base_air_source view (3 : Fin 15), base_air_source view (4 : Fin 15),
      base_air_source view (5 : Fin 15), base_air_source view (6 : Fin 15),
      base_air_source view (7 : Fin 15), base_air_source view (8 : Fin 15),
      base_air_source view (9 : Fin 15), base_air_source view (10 : Fin 15),
      base_air_source view (11 : Fin 15), base_air_source view (12 : Fin 15),
      base_air_source view (13 : Fin 15), base_air_source view (14 : Fin 15),
      direct_source view (0 : Fin 6), direct_source view (1 : Fin 6),
      direct_source view (2 : Fin 6), direct_source view (3 : Fin 6),
      direct_source view (4 : Fin 6), direct_source view (5 : Fin 6),
      CompleteView.polynomialRow,
      PolynomialRow.residual, PolynomialRow.residual24, PolynomialRow.residual25,
      PolynomialRow.residual26, PolynomialRow.residual27, PolynomialRow.residual28,
      PolynomialRow.residual29, PolynomialRow.residual30, PolynomialRow.residual31,
      PolynomialRow.residual32, PolynomialRow.highDen, PolynomialRow.dualStepDen,
      PolynomialRow.lowDen, PolynomialRow.primaryDen, PolynomialRow.dualDen,
      PolynomialRow.previousDen, PolynomialRow.nextDen,
      ← Ext3.ofBase_add, ← Ext3.ofBase_sub, ← Ext3.ofBase_mul,
      ← Ext3.ofBase_neg, ← Ext3.ofBase_zero, ← Ext3.ofBase_one]

/-- GROUP0, next physical L1 and all six direct blocks in their source order. -/
theorem finalizer_polynomial_source (view : DecodedView resolved)
    (row : view.complete.Index) :
    Stage2.polynomial? resolved row.val constraint_Mem_33 =
      some ((view.complete.polynomialRow row).residual33) := by
  rw [SourceFinalizer.compiled_constraint_eq_expected]
  simp [SourceFinalizer.expectedConstraint, Stage2.polynomial?,
    view.complete.polynomial_l1_next row, view.groupValue_source,
    view.complete.auxiliary_source row (0 : Fin 3) 0,
    direct_source view (0 : Fin 6), direct_source view (1 : Fin 6),
    direct_source view (2 : Fin 6), direct_source view (3 : Fin 6),
    direct_source view (4 : Fin 6), direct_source view (5 : Fin 6),
    CompleteView.polynomialRow, PolynomialRow.residual33, PolynomialRow.directSum]

private theorem mem_scope (view : DecodedView resolved) :
    SourceFinalizer.memOccurrence resolved = true := by
  have scope := view.complete.base.registry_scope
  simp [SourceFinalizer.memOccurrence, scope.1, scope.2]

theorem nonlinear_source (view : DecodedView resolved) (row : view.complete.Index)
    (equation : Fin 9) :
    Stage2.evaluate? resolved row.val (actualNonlinear equation) =
      some ((view.complete.polynomialRow row).residual equation) := by
  simp only [Stage2.evaluate?, view.mem_scope, ↓reduceIte]
  exact view.nonlinear_polynomial_source row equation

theorem finalizer_source (view : DecodedView resolved) (row : view.complete.Index) :
    Stage2.evaluate? resolved row.val constraint_Mem_33 =
      some ((view.complete.polynomialRow row).residual33) := by
  simp only [Stage2.evaluate?, view.mem_scope, ↓reduceIte]
  exact view.finalizer_polynomial_source row

/-- Equality is coefficientwise for ALL three coordinates, not just c0. -/
theorem nonlinear_coefficient_source (view : DecodedView resolved)
    (row : view.complete.Index) (equation : Fin 9) (coordinate : Fin 3) :
    (Stage2.evaluate? resolved row.val (actualNonlinear equation)).map
      (fun value => value.coeff coordinate) =
      some (((view.complete.polynomialRow row).residual equation).coeff coordinate) := by
  rw [view.nonlinear_source row equation]
  rfl

theorem finalizer_coefficient_source (view : DecodedView resolved)
    (row : view.complete.Index) (coordinate : Fin 3) :
    (Stage2.evaluate? resolved row.val constraint_Mem_33).map
      (fun value => value.coeff coordinate) =
      some (((view.complete.polynomialRow row).residual33).coeff coordinate) := by
  rw [view.finalizer_source row]
  rfl

/-- Exact decoding/model equation equivalence, never old-domain -> new-domain. -/
theorem nonlinear_zero_iff (view : DecodedView resolved) (row : view.complete.Index)
    (equation : Fin 9) :
    Stage2.evaluate? resolved row.val (actualNonlinear equation) = some 0 ↔
      (view.complete.polynomialRow row).residual equation = 0 := by
  rw [view.nonlinear_source row equation, Option.some.injEq]

theorem finalizer_zero_iff (view : DecodedView resolved) (row : view.complete.Index) :
    Stage2.evaluate? resolved row.val constraint_Mem_33 = some 0 ↔
      (view.complete.polynomialRow row).residual33 = 0 := by
  rw [view.finalizer_source row, Option.some.injEq]

end DecodedView
end ZiskFv.AirsClean.Mem.PhysicalSource
