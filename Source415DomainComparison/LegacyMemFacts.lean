import Source458DomainComparison.LegacyMem
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections

/-!
# Historical Mem facts, derived from the historical verifier

The old comparison retains its scalar constraints24--33, not merely the new
segment projection. These facts use the historical component's actual D0/D1,
original materialized rows, original data, and the same fixed-column schema.
They are not a production Mem acceptance certificate or a new-to-old transport.
-/
namespace ZiskFv.AirsClean.FullEnsemble.HistoricalMemFacts

open Goldilocks Air.Flat

/-- The literal retired scalar decoder, confined to historical comparisons. -/
@[reducible]
def memPermutationOfTableData (table : Table FGL) :
    ZiskFv.AirsClean.Mem.Legacy457.PermutationColumns FGL :=
  ZiskFv.AirsClean.Mem.Legacy457.permutationColumnsOfProverDataAndFixed table.data
    (fun row => table.fixedAt ZiskFv.AirsClean.Mem.MemFixedColumn.l1 row)

theorem generatedTransition_iff_canonicalTableData
    (table : Table FGL)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus)
    (idx : Fin table.length) :
    ZiskFv.AirsClean.Mem.Legacy457.generatedTransition ZiskFv.AirsClean.Mem.memFixedColumns idx.val
        (table.previousEnvironment idx) (table.environmentAt idx) ↔
      (ZiskFv.Airs.Mem.segmentResidualEveryRow
          (memSegmentOfTableData table) (memOfTableData table) idx.val
        ∧ ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row
          (memSegmentOfTableData table) (memPermutationOfTableData table)
          (memOfTableData table) idx.val
        ∧ ZiskFv.AirsClean.Mem.memRangeSidecarBridge (table.environmentAt idx)) := by
  rcases table with ⟨component, rawRows, data, raw_uniform_width, fixed_domain⟩
  change component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus at h_component
  subst component
  let table : Table FGL :=
    { component := ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus
      rawRows := rawRows
      data := data
      raw_uniform_width := raw_uniform_width
      fixed_domain := fixed_domain }
  change ZiskFv.AirsClean.Mem.Legacy457.generatedTransition
      ZiskFv.AirsClean.Mem.memFixedColumns idx.val
      (table.previousEnvironment idx) (table.environmentAt idx) ↔
    (ZiskFv.Airs.Mem.segmentResidualEveryRow
        (memSegmentOfTableData table) (memOfTableData table) idx.val
      ∧ ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row
        (memSegmentOfTableData table) (memPermutationOfTableData table)
        (memOfTableData table) idx.val
      ∧ ZiskFv.AirsClean.Mem.memRangeSidecarBridge (table.environmentAt idx))
  have h_fixed_at : ∀ slot row : Nat,
      table.fixedAt slot row =
        ZiskFv.AirsClean.Mem.memFixedColumns.fixedAt slot row := by
    intro slot row
    rfl
  have h_current :
      ZiskFv.AirsClean.Mem.memRowFromEnvironment (table.environmentAt idx) =
        ZiskFv.AirsClean.Mem.rowAt (memOfTableData table) idx.val := by
    rw [memRowFromEnvironmentAt_eq_memTableRowAtOrZero]
  have h_previous :
      ZiskFv.AirsClean.Mem.memRowFromEnvironment (table.previousEnvironment idx) =
        ZiskFv.AirsClean.Mem.rowAt (memOfTableData table) (idx.val - 1) := by
    rw [memRowFromPreviousEnvironment_eq_memTableRowAtOrZero]
  have h_data : (table.environmentAt idx).data = table.data := rfl
  by_cases h_zero : idx.val = 0
  · simp only [ZiskFv.AirsClean.Mem.Legacy457.generatedTransition,
      ZiskFv.AirsClean.Mem.memWindow]
    rw [h_current, h_previous, h_data]
    have h_previous_eq : idx.val - 1 = idx.val := by omega
    simp only [memSegmentOfTableData, memPermutationOfTableData, h_fixed_at,
      h_previous_eq, ite_true, ite_false, ZiskFv.AirsClean.Mem.rowAt,
      ZiskFv.Airs.Mem.segmentResidualEveryRow, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.delta_addr, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1,
      ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_1,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_step,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_0,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_primary_mem,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_mem,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_accumulator_delta]
  · have h_previous_ne : idx.val - 1 ≠ idx.val := by omega
    simp only [ZiskFv.AirsClean.Mem.Legacy457.generatedTransition,
      ZiskFv.AirsClean.Mem.memWindow]
    rw [h_current, h_previous, h_data]
    simp only [memSegmentOfTableData, memPermutationOfTableData, h_fixed_at,
      if_neg h_previous_ne, ite_true, ite_false, ZiskFv.AirsClean.Mem.rowAt,
      ZiskFv.Airs.Mem.segmentResidualEveryRow, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.delta_addr, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1,
      ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_1,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_step,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_0,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_primary_mem,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_mem,
      ZiskFv.AirsClean.Mem.Legacy457.gsum_accumulator_delta]

theorem memTableGeneratedRangeFacts_of_component_constraints
    (table : Table FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus)
    (h_constraints : table.Constraints) :
    MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1) := by
  have rangeAt : ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.dualMemRowRangeFacts
        (eval (table.environment (table.table.get idx))
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    intro idx
    have h_mem : table.table.get idx ∈ table.table :=
      List.mem_iff_get.mpr ⟨idx, rfl⟩
    have h_holds : table.component.operations.ConstraintsHold
        (table.environment (table.table.get idx)) :=
      h_constraints (table.table.get idx) h_mem
    rw [h_component] at h_holds
    exact ZiskFv.AirsClean.Mem.dualMemRowRangeFacts_of_componentWithDualMemBus_constraints
      _ h_holds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro idx
    have h := rangeAt idx
    rw [← rowAt_memOfTable table gsum im0 im1 idx] at h
    exact ⟨h.1, h.2.1⟩
  · intro idx
    have h := rangeAt idx
    rw [← rowAt_memOfTable table gsum im0 im1 idx] at h
    exact h.2.2.1
  · intro idx
    have h := rangeAt idx
    rw [← rowAt_memOfTable table gsum im0 im1 idx] at h
    exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · intro idx
    have h := rangeAt idx
    rw [← rowAt_memOfTable table gsum im0 im1 idx] at h
    exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩
  · intro idx h_sel_dual
    have h := rangeAt idx
    rw [← rowAt_memOfTable table gsum im0 im1 idx] at h
    exact h.2.2.2.2.2.2.2.2 h_sel_dual

/-- D0 range facts require no retired numeric equations. -/
theorem memTableGeneratedRangeFacts_of_component_constraints_canonical
    (table : Table FGL)
    (h_component : table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus)
    (h_constraints : table.Constraints) :
    MemTableGeneratedRangeFacts table (memOfTableData table) :=
  memTableGeneratedRangeFacts_of_component_constraints table _ _ _ h_component h_constraints

structure MemTableGeneratedConstraintFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.AirsClean.Mem.Legacy457.PermutationColumns FGL) : Prop where
  segmentAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.segment_every_row segment mem idx.val
  permutationAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row segment permutation mem idx.val

/-- Derive the full generated Mem constraint surface from one live table.

The component's ordinary constraints supply the nine row-local equations; its
right-indexed transition supplies the remaining segment residual and all
permutation equations. Both paths read the same materialized rows, selected
`ProverData`, and component-owned fixed schema. -/
theorem memTableGeneratedConstraintFacts_of_component_constraints_transitions
    (table : Table FGL)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus)
    (h_constraints : table.Constraints)
    (h_transitions : table.TransitionConstraints) :
    MemTableGeneratedConstraintFacts
      table (memOfTableData table) (memSegmentOfTableData table)
      (memPermutationOfTableData table) := by
  have transitionFacts : ∀ idx : Fin table.length,
      ZiskFv.Airs.Mem.segmentResidualEveryRow
          (memSegmentOfTableData table) (memOfTableData table) idx.val
        ∧ ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row
          (memSegmentOfTableData table) (memPermutationOfTableData table)
          (memOfTableData table) idx.val := by
    intro idx
    have h_transition := (generatedTransition_iff_canonicalTableData table h_component idx).mp
      (by simpa only [h_component, ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus] using
        h_transitions idx)
    exact ⟨h_transition.1, h_transition.2.1⟩
  refine ⟨?_, ?_⟩
  · intro idx
    have h_mem : table.table.get idx ∈ table.table :=
      List.mem_iff_get.mpr ⟨idx, rfl⟩
    have h_holds : table.component.operations.ConstraintsHold
        (table.environment (table.table.get idx)) :=
      h_constraints (table.table.get idx) h_mem
    rw [h_component] at h_holds
    have h_spec :=
      ZiskFv.AirsClean.Mem.spec_of_componentWithDualMemBus_constraints
        (table.environment (table.table.get idx)) h_holds
    have h_row_spec : ZiskFv.AirsClean.Mem.Spec
        (ZiskFv.AirsClean.Mem.rowAt (memOfTableData table) idx.val) := by
      rw [rowAt_memOfTableData table idx]
      exact h_spec
    have h_core : ZiskFv.Airs.Mem.core_every_row (memOfTableData table) idx.val := by
      simpa [ZiskFv.Airs.Mem.core_every_row, ZiskFv.AirsClean.Mem.Spec,
        ZiskFv.AirsClean.Mem.rowAt] using h_row_spec
    let transitionIdx : Fin table.length := ⟨idx.val, by
      simpa only [Table.table_length] using idx.isLt⟩
    exact ZiskFv.Airs.Mem.segment_every_row_of_core_and_residual
      h_core (transitionFacts transitionIdx).1
  · intro idx
    let transitionIdx : Fin table.length := ⟨idx.val, by
      simpa only [Table.table_length] using idx.isLt⟩
    exact (transitionFacts transitionIdx).2

end ZiskFv.AirsClean.FullEnsemble.HistoricalMemFacts
