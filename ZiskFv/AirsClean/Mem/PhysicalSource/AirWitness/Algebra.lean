import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.Data
import ZiskFv.AirsClean.Mem.Spec

/-! Chosen-image algebra for the full source-owned physical Mem domain.
The running sum is the explicit arithmetic progression in Data; neither its
recurrence nor its physical-last finalizer is a premise. All extension
identities use the existing three-coefficient base embedding, not an extension
Field instance. Source: b632 mem.pil103–175,195–241,263–286,365–397,403–440;
proofman ff0e33a9 std_sum.pil571–599,640–696. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open Stage2

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- The next pulse selects the actual physical last row, including its cyclic
rotation to zero. It is not a populated-prefix boundary. -/
theorem firstFlag_next (view : View resolved) (row : Index) :
    firstFlag (view.next row) = if row.val + 1 = N then 1 else 0 := by
  exact Option.some.inj ((view.actual_l1 (view.next row)).symm.trans (view.shifted_l1 row))

/-- Row zero uses the actual cyclic predecessor. The pulse cancels that
predecessor's running value; positive rows use the physical predecessor index. -/
theorem running_step (view : View resolved) (row : Index) :
    running row - running (view.previous row) * Ext3.ofBase (1 - firstFlag row) =
      Ext3.ofBase delta := by
  simp only [running, ← Ext3.ofBase_mul, ← Ext3.ofBase_sub]
  apply congrArg Ext3.ofBase
  by_cases zero : row.val = 0
  · have first : row = view.first := Fin.ext zero
    rw [first, view.previous_first]
    simp [firstFlag, View.first]
  · have positive : 0 < row.val := by omega
    have previous : (view.previous row).val + 1 = row.val := by
      rw [view.previous_of_positive row positive]
      omega
    simp only [firstFlag, if_neg zero, sub_zero, mul_one, previous,
      Nat.cast_add, Nat.cast_one]
    ring

/-- Every one of the independent c0–c23 segment clauses holds, including row
zero and all clauses with actual previous/next source rotations. -/
theorem segment_satisfies (view : View resolved) (row : Index) (equation : Fin 24) :
    segmentResidual view row equation = 0 := by
  by_cases zero : row.val = 0 <;> fin_cases equation <;>
    norm_num [segmentResidual, primary, baseAir, firstFlag, zero, address, previousAddress]

private theorem direct_zero : direct 0 = Ext3.ofBase (-((12 : FGL)⁻¹)) := rfl
private theorem direct_one : direct 1 = 0 := rfl
private theorem direct_two : direct 2 = Ext3.ofBase cluster := rfl
private theorem direct_three : direct 3 = Ext3.ofBase cluster := rfl
private theorem direct_four : direct 4 = Ext3.ofBase cluster := rfl
private theorem direct_five : direct 5 = Ext3.ofBase cluster := rfl

/-- All nine nonlinear identities and the full three-coefficient finalizer.
The independently closed group expression is proved equal to the arithmetic
progression plus the six direct terms at the true physical last row. -/
theorem stage2_satisfies (view : View resolved) (row : Index) :
    (polynomialRow view row).WithFinalizer := by
  have h104 : (104 : FGL) ≠ 0 := by decide
  have h105 : (105 : FGL) ≠ 0 := by decide
  have h12 : (12 : FGL) ≠ 0 := by decide
  unfold PolynomialRow.WithFinalizer PolynomialRow.Circuit
  refine ⟨⟨?_, ?_, ?recurrence, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?finalizer⟩
  case recurrence =>
    simp only [PolynomialRow.residual26, PolynomialRow.lowDen, polynomialRow]
    rw [running_step]
    simp only [delta, cluster, alpha, gamma,
      ← Ext3.ofBase_zero, ← Ext3.ofBase_add, ← Ext3.ofBase_sub,
      ← Ext3.ofBase_mul, ← Ext3.ofBase_neg]
    apply congrArg Ext3.ofBase
    field_simp [h104, h105] <;> ring
  case finalizer =>
    simp only [PolynomialRow.residual33, PolynomialRow.directSum, polynomialRow,
      firstFlag_next, groupResult, running, direct_zero, direct_one, direct_two,
      direct_three, direct_four, direct_five, cluster,
      ← Ext3.ofBase_zero, ← Ext3.ofBase_add, ← Ext3.ofBase_sub,
      ← Ext3.ofBase_mul, ← Ext3.ofBase_neg]
    apply congrArg Ext3.ofBase
    by_cases atLast : row.val + 1 = N
    · simp only [atLast, ↓reduceIte, one_mul, delta]
      ring
    · simp only [if_neg atLast, zero_mul]
  all_goals
    simp only [PolynomialRow.residual24, PolynomialRow.residual25,
      PolynomialRow.residual27, PolynomialRow.residual28, PolynomialRow.residual29,
      PolynomialRow.residual30, PolynomialRow.residual31, PolynomialRow.residual32,
      PolynomialRow.highDen, PolynomialRow.dualStepDen, PolynomialRow.lowDen,
      PolynomialRow.primaryDen, PolynomialRow.dualDen, PolynomialRow.previousDen,
      PolynomialRow.nextDen, polynomialRow, alpha, gamma, cluster,
      direct_zero, direct_one, direct_two, direct_three, direct_four, direct_five,
      ← Ext3.ofBase_zero, ← Ext3.ofBase_add, ← Ext3.ofBase_sub,
      ← Ext3.ofBase_mul, ← Ext3.ofBase_neg]
  all_goals
    first
    | rfl
    | apply congrArg Ext3.ofBase
      field_simp [h104, h105, h12] <;> ring

/-- The exact declared scalar widths, four distance16 calls, increment ranges,
and selector-aware dual24 call all hold for the chosen image. -/
theorem local_lookups (row : Index) : LocalLookups row := by
  unfold LocalLookups
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro column
    by_cases zero : row.val = 0 <;> fin_cases column <;>
      norm_num [primary, firstFlag, zero, address, Stage1.SourceColumns.packedWidth]
  · intro index
    fin_cases index <;> norm_num [baseAir]
  · norm_num [primary]
  · norm_num [primary]
  · simp [primary]

/-- The original primary-row Mem specification, without new assumptions. -/
theorem primary_spec (row : Index) : Mem.Spec (primaryRow row) := by
  by_cases zero : row.val = 0 <;>
    norm_num [Mem.Spec, primaryRow, primary, firstFlag, zero]

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness
