import ZiskFv.AirsClean.Mem.PhysicalSource.Columns
import ZiskFv.AirsClean.Mem.Stage2.PolynomialRow
import ZiskFv.AirsClean.Mem.Stage2.PackedSource
import ZiskFv.AirsClean.Mem.Stage2.Equations
import ZiskFv.AirsClean.Mem.Stage2.Literals

/-! Generic physical polynomial data, not the chosen AirWitness image. Every
field comes from the SAME computed CompleteView and original source buffers.
No satisfaction, native/PIL-id agreement or missing-cell defaults are assumed.
The native-layout base AIR fields exist because even the first checked direct
block begins AFTER the fifteen scalar source fields. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Stage2

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

namespace CompleteView

private theorem first_direct_exists (view : CompleteView resolved) :
    ∃ words, ZiskFv.AirsClean.NativeValuesLayout.memInverseWords? 0
      (resolved.params false) = some words := by
  cases selected : ZiskFv.AirsClean.NativeValuesLayout.memInverseWords? 0
      (resolved.params false) with
  | none =>
    have all := view.base.directSelected
    simp only [directBatch?, selected, bind, Option.bind_none] at all
  | some words => exact ⟨words, selected⟩

/-- A source-storage consequence, NOT an additional validator or value bound. -/
theorem base_air_capacity (view : CompleteView resolved) :
    15 < (resolved.params false).airvalues.size := by
  obtain ⟨words, selected⟩ := view.first_direct_exists
  by_contra missing
  have absent : (resolved.params false).airvalues[15]? = none :=
    getElem?_neg (resolved.params false).airvalues 15 (by omega)
  rw [ZiskFv.AirsClean.NativeValuesLayout.mem_inverse_reads_actual_buffer] at selected
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, absent, bind,
    Option.bind_none] at selected

/-- Original scalar AIR storage; no rebasing, copied row table or fallback. -/
def baseAir (view : CompleteView resolved) (column : Fin 15) : FGL :=
  (resolved.params false).airvalues[column.val]'(by
    have capacity := view.base_air_capacity
    have within := column.isLt
    omega)

/-- Independent model data for EVERY view, retaining all three coefficients,
actual cyclic predecessor/next pulse, GROUP0 and all six direct blocks. -/
def polynomialRow (view : CompleteView resolved) (row : view.Index) : PolynomialRow where
  addr := view.scalar row 0
  step := view.scalar row 1
  sel := view.scalar row 2
  stepDual := view.scalar row 4
  selDual := view.scalar row 5
  valueLo := view.scalar row 6
  valueHi := view.scalar row 7
  wr := view.scalar row 8
  lowIncrement := view.scalar row 10
  highIncrement := view.scalar row 11
  segmentId := view.baseAir 0
  isLastSegment := view.baseAir 2
  previousValueLo := view.baseAir 3
  previousValueHi := view.baseAir 4
  previousStep := view.baseAir 5
  previousAddr := view.baseAir 6
  lastValueLo := view.baseAir 7
  lastValueHi := view.baseAir 8
  lastStep := view.baseAir 9
  lastAddr := view.baseAir 10
  distanceBaseLo := view.baseAir 11
  distanceBaseHi := view.baseAir 12
  distanceEndLo := view.baseAir 13
  distanceEndHi := view.baseAir 14
  alpha := view.challenge 0
  gamma := view.challenge 1
  running := view.auxiliary row 0 0
  previousRunning := view.auxiliary row 0 (-1)
  cluster0 := view.auxiliary row 1 0
  cluster1 := view.auxiliary row 2 0
  direct0 := view.direct 0
  direct1 := view.direct 1
  direct2 := view.direct 2
  direct3 := view.direct 3
  direct4 := view.direct 4
  direct5 := view.direct 5
  l1 := view.l1 row
  nextL1 := view.l1 (view.base.next row)
  groupResult := view.group

theorem polynomial_running_source (view : CompleteView resolved) (row : view.Index) :
    witness? resolved row.val 2 0 0 = some (view.polynomialRow row).running :=
  view.auxiliary_source row 0 0

theorem polynomial_previous_running_source (view : CompleteView resolved) (row : view.Index) :
    witness? resolved row.val 2 0 (-1) = some (view.polynomialRow row).previousRunning :=
  view.auxiliary_source row 0 (-1)

theorem polynomial_cluster_sources (view : CompleteView resolved) (row : view.Index) :
    witness? resolved row.val 2 1 0 = some (view.polynomialRow row).cluster0 ∧
    witness? resolved row.val 2 2 0 = some (view.polynomialRow row).cluster1 :=
  ⟨view.auxiliary_source row 1 0, view.auxiliary_source row 2 0⟩

theorem polynomial_running_coefficient (view : CompleteView resolved) (row : view.Index)
    (coordinate : Fin 3) :
    ((view.polynomialRow row).running).coeff coordinate =
      resolved.slotData.auxTrace[view.auxiliaryAddress row 0 0 coordinate] :=
  view.auxiliary_coeff row 0 0 coordinate

theorem polynomial_previous_running_coefficient (view : CompleteView resolved)
    (row : view.Index) (coordinate : Fin 3) :
    ((view.polynomialRow row).previousRunning).coeff coordinate =
      resolved.slotData.auxTrace[view.auxiliaryAddress row 0 (-1) coordinate] :=
  view.auxiliary_coeff row 0 (-1) coordinate

theorem polynomial_finalizer_eq (view : CompleteView resolved) (row : view.Index) :
    (view.polynomialRow row).residual33 = view.finalizerResidual row := rfl

/-- All coefficients, not a scalar or c0-only finalizer claim. -/
theorem polynomial_finalizer_coefficients (view : CompleteView resolved)
    (row : view.Index) :
    (view.polynomialRow row).residual33 = 0 ↔
      ∀ coordinate : Fin 3, (view.finalizerResidual row).coeff coordinate = 0 := by
  rw [view.polynomial_finalizer_eq]
  exact view.finalizer_coefficients row

private theorem scalar_block (params : Params FGL) (values : Array FGL) (offset : Nat)
    (selected : buffer? params .fixed = some values) (bound : offset < values.size) :
    Stage2.baseWords? (readBlock? params .fixed offset 1) =
      some (Ext3.ofBase values[offset]) := by
  have covered : offset + 1 ≤ values.size := by omega
  simp [Stage2.baseWords?, SourceFinalizer.scalarWord?, readBlock?, selected,
    covered, bound, Array.size_extract, Array.getElem_extract]

/-- Actual source fixed column1 at ANY signed cyclic rotation. -/
theorem polynomial_l1_source (view : CompleteView resolved) (row : view.Index)
    (rotation : Int) :
    Stage2.fixed? resolved row.val 1 rotation =
      some (Ext3.ofBase (view.l1 (view.base.rotate row rotation))) := by
  have selected : buffer? (resolved.params false) .fixed =
      some resolved.slotData.fixed := by
    simp only [buffer?, ResolvedOccurrence.params, paramsOf]
  have bound : (view.base.rotate row rotation).val * 2 + 1 <
      resolved.slotData.fixed.size := by
    have coverage := view.base.fixed_coverage
    have within : (view.base.rotate row rotation).val < view.base.count :=
      (view.base.rotate row rotation).isLt
    omega
  unfold Stage2.fixed?
  rw [if_pos (by decide : (1 : Nat) < 2)]
  simp only [ResolvedOccurrence.fixedWords?, bind, view.base.setupSelected,
    Option.bind_some, view.base.native_rotation row rotation, view.base.fixed_width]
  rw [if_pos (by decide : (1 : Nat) < 2)]
  rw [scalar_block _ _ _ selected bound]
  apply congrArg (fun value : FGL => some (Ext3.ofBase value))
  unfold l1
  exact getElem_congr_idx (by omega)

theorem polynomial_l1_current (view : CompleteView resolved) (row : view.Index) :
    Stage2.fixed? resolved row.val 1 0 =
      some (Ext3.ofBase (view.polynomialRow row).l1) := by
  rw [view.polynomial_l1_source, view.base.rotate_zero]
  rfl

theorem polynomial_l1_next (view : CompleteView resolved) (row : view.Index) :
    Stage2.fixed? resolved row.val 1 1 =
      some (Ext3.ofBase (view.polynomialRow row).nextL1) := by
  rw [view.polynomial_l1_source, view.base.rotate_one]
  rfl

end CompleteView
end ZiskFv.AirsClean.Mem.PhysicalSource
