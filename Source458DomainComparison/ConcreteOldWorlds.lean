import Source458DomainComparison.Accepted18
import ZiskFv.Compliance.SingleAddWitness
import ZiskFv.Compliance.AddSpinWitness
import ZiskFv.Compliance.AddAddiSpinWitness
import ZiskFv.Compliance.AddFaithfulPaddedWitness
import ZiskFv.Compliance.JalrSpinWitness
import ZiskFv.Compliance.SdLdSpinWitness
import ZiskFv.Compliance.DivSpinWitness

/-!
# Genuine historical457 concrete worlds

The seven cases below are fixed original examples, not an inverse transport
from an arbitrary corrected accepted trace. Each world is constructed afresh
with the historical Mem component. Every raw buffer, source-provider row, data
key, fixed value, table position and public input is retained. The six empty
Mem cases have vacuous old D1. The two actual Sd/Ld Mem rows instead have a
separate proof of the literal old scalar equations on the original numeric
values. In particular no corrected Mem D1 is used to reconstruct those values.
-/
namespace ZiskFv.Compliance.Legacy457.ConcreteOldWorlds

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.Mem
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Compliance.Instantiation

noncomputable section

inductive Example where
  | singleAdd | addSpin | addAddiSpin | addFaithful | jalr | sdLd | divSpin

private def instructionCount : Example → Nat
  | .singleAdd => 1
  | .addSpin => 2
  | .addAddiSpin => 3
  | .addFaithful => 1
  | .jalr => 2
  | .sdLd => 7
  | .divSpin => 4

/-- Only the fixed original concrete records supply source buffers and the
unchanged non-Mem certificates. This is not a caller-supplied witness. -/
private def sourceTrace : (example : Example) →
    ZiskFv.Compliance.AcceptedZiskTrace (instructionCount example)
  | .singleAdd => SingleAddWitness.singleAddAcceptedTrace
  | .addSpin => AddSpinWitness.addSpinAcceptedTrace
  | .addAddiSpin => AddAddiSpinWitness.addAddiSpinAcceptedTrace
  | .addFaithful => AddFaithfulPaddedWitness.addFaithfulAcceptedTrace
  | .jalr => JalrSpinWitness.jalrAcceptedTrace
  | .sdLd => SdLdSpinWitness.sdLdAcceptedTrace
  | .divSpin => DivSpinWitness.divSpinAcceptedTrace

/-- A data carrier only: this has no theorem reconstructing arbitrary old D1. -/
private def historicalTable (table : Table FGL) : Table FGL := by
  classical
  exact if h : table.component = Mem.componentWithDualMemBus then
    { component := Mem.Legacy457.componentWithDualMemBus
      rawRows := table.rawRows
      data := table.data
      raw_uniform_width := by
        intro row hr
        simpa only [h] using table.raw_uniform_width row hr
      fixed_domain := by
        intro columns hc
        have domain := table.fixed_domain
        rw [h] at domain
        exact domain columns hc }
    else table

private theorem historicalTable_of_ne (table : Table FGL)
    (h : table.component ≠ Mem.componentWithDualMemBus) :
    historicalTable table = table := by
  classical
  simp only [historicalTable, dif_neg h]

private theorem historicalTable_mem_component (table : Table FGL)
    (h : table.component = Mem.componentWithDualMemBus) :
    (historicalTable table).component = Mem.Legacy457.componentWithDualMemBus := by
  classical
  simp only [historicalTable, dif_pos h]

@[simp] private theorem historicalTable_rawRows (table : Table FGL) :
    (historicalTable table).rawRows = table.rawRows := by
  classical
  unfold historicalTable
  split <;> rfl

@[simp] private theorem historicalTable_data (table : Table FGL) :
    (historicalTable table).data = table.data := by
  classical
  unfold historicalTable
  split <;> rfl

@[simp] private theorem historicalTable_length (table : Table FGL) :
    (historicalTable table).length = table.length := by
  simp only [Table.length, historicalTable_rawRows]

@[simp] private theorem historicalTable_rawWidth (table : Table FGL) :
    (historicalTable table).component.rawWidth = table.component.rawWidth := by
  classical
  unfold historicalTable
  split
  · rename_i h
    rw [h] <;> rfl
  · rfl

@[simp] private theorem historicalTable_table (table : Table FGL) :
    (historicalTable table).table = table.table := by
  classical
  rcases table with ⟨component, rawRows, data, uniform, domain⟩
  unfold historicalTable
  split
  · rename_i h
    change component = Mem.componentWithDualMemBus at h
    subst component
    rfl
  · rfl

@[simp] private theorem historicalTable_fixedAt (table : Table FGL) (slot row : Nat) :
    (historicalTable table).fixedAt slot row = table.fixedAt slot row := by
  classical
  rcases table with ⟨component, rawRows, data, uniform, domain⟩
  unfold historicalTable
  split
  · rename_i h
    change component = Mem.componentWithDualMemBus at h
    subst component
    rfl
  · rfl

@[simp] private theorem historicalTable_environment (table : Table FGL) (row : Array FGL) :
    (historicalTable table).environment row = table.environment row := by
  simp only [Table.environment, historicalTable_data]

private theorem historicalListGet_of_eq {α : Type*} {left right : List α}
    (rows : left = right) (index : Nat)
    (leftBound : index < left.length) (rightBound : index < right.length) :
    left.get ⟨index, leftBound⟩ = right.get ⟨index, rightBound⟩ := by
  cases rows
  rfl

@[simp] private theorem historicalTable_environmentAt (table : Table FGL)
    (index : Fin (historicalTable table).length) :
    (historicalTable table).environmentAt index =
      table.environmentAt ⟨index.val, by simpa only [historicalTable_length] using index.isLt⟩ := by
  simp only [Table.environmentAt, historicalTable_environment]
  exact congrArg table.environment
    (historicalListGet_of_eq (historicalTable_table table) index.val
      (by simpa only [Table.table_length] using index.isLt)
      (by simpa only [Table.table_length, historicalTable_length] using index.isLt))

@[simp] private theorem historicalTable_successorEnvironment (table : Table FGL)
    (index : Fin (historicalTable table).length) :
    (historicalTable table).successorEnvironment index = table.successorEnvironment
      ⟨index.val, by simpa only [historicalTable_length] using index.isLt⟩ := by
  simp only [Table.successorEnvironment, Table.successorIndex,
    historicalTable_environmentAt, historicalTable_length]

@[simp] private theorem historicalTable_operations (table : Table FGL) :
    (historicalTable table).component.operations = table.component.operations := by
  classical
  unfold historicalTable
  split
  · rename_i h
    rw [h] <;> rfl
  · rfl

@[simp] private theorem historicalTable_cyclic (table : Table FGL) :
    (historicalTable table).component.cyclicSuccessorTransition =
      table.component.cyclicSuccessorTransition := by
  classical
  unfold historicalTable
  split
  · rename_i h
    rw [h] <;> rfl
  · rfl

private theorem historicalTable_component_of_width (table : Table FGL)
    (component : Component FGL) (hc : table.component = component)
    (hw : component.rawWidth ≠ 17) : (historicalTable table).component = component := by
  apply Eq.trans (congrArg Table.component (historicalTable_of_ne table ?_)) hc
  intro hm
  apply hw
  rw [← hc, hm] <;> rfl

/-- A real old18 witness with all seventeen original physical carriers. -/
def witness (example : Example) : EnsembleWitness
    (FullEnsemble.Legacy457.fullRv64imEnsemble
      (sourceTrace example).programLength (sourceTrace example).program).ensemble where
  tables := (sourceTrace example).witness.tables.map historicalTable
  data := (sourceTrace example).witness.data
  publicInput := (sourceTrace example).witness.publicInput
  same_length := by
    rw [List.length_map, ← (sourceTrace example).witness.same_length] <;> rfl
  same_circuits := by
    intro index hi
    have sourceBound : index <
        (FullEnsemble.fullRv64imEnsemble (sourceTrace example).programLength
          (sourceTrace example).program).ensemble.tables.length := by
      change index < 17
      change index < 17 at hi
      exact hi
    rw [List.getElem_map]
    have bound : index < 17 := by change index < 17 at hi; exact hi
    interval_cases index
    all_goals first
      | exact (historicalTable_mem_component _
          ((sourceTrace example).witness.same_circuits _ sourceBound).symm).symm
      | (symm
         apply historicalTable_component_of_width _ _
           ((sourceTrace example).witness.same_circuits _ sourceBound).symm
         exact of_decide_eq_true rfl)
  same_data := by
    intro table ht
    rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
    rw [historicalTable_data]
    exact (sourceTrace example).witness.same_data source hs

private theorem witness_verifierTable (example : Example) :
    (witness example).verifierTable = (sourceTrace example).witness.verifierTable := by
  apply Ensemble.verifierTable_ext <;> rfl

private theorem historicalTable_verifierTable (example : Example) :
    historicalTable (sourceTrace example).witness.verifierTable =
      (sourceTrace example).witness.verifierTable := by
  apply historicalTable_of_ne
  intro h
  have hw := congrArg (fun c : Component FGL => c.rawWidth) h
  change (0 : Nat) = 17 at hw
  omega

private theorem witness_allTables (example : Example) :
    (witness example).allTables =
      (sourceTrace example).witness.allTables.map historicalTable := by
  simp only [EnsembleWitness.allTables, List.map_cons,
    historicalTable_verifierTable, witness_verifierTable] <;> rfl

/-- Original buffers, in their exact original physical order. -/
theorem witness_rawRows (example : Example) :
    (witness example).tables.map Table.rawRows =
      (sourceTrace example).witness.tables.map Table.rawRows := by
  simp only [witness, List.map_map, Function.comp_def, historicalTable_rawRows]

/-- In particular the original Sd/Ld scalar data is retained, not recomputed. -/
theorem witness_data (example : Example) :
    (witness example).data = (sourceTrace example).witness.data := rfl

/-- Non-Mem original tables, including Main and the two complete providers,
are preserved as exact objects, not only as decoded row lists. -/
theorem sourceTable_preserved (example : Example) (table : Table FGL)
    (ht : table ∈ (sourceTrace example).witness.tables)
    (hw : table.component.rawWidth ≠ 17) : table ∈ (witness example).tables := by
  apply List.mem_map.mpr
  refine ⟨table, ht, historicalTable_of_ne table ?_⟩
  intro hm
  apply hw
  rw [hm] <;> rfl

private theorem source_mem_component_of_width (example : Example) (table : Table FGL)
    (ht : table ∈ (sourceTrace example).witness.allTables)
    (hw : table.component.rawWidth = 17) : table.component = Mem.componentWithDualMemBus := by
  have hc := EnsembleWitness.mem_allTables_component_of_mem_allTables ht
  rcases List.mem_iff_get.mp hc with ⟨⟨index, bound⟩, source⟩
  have width :
      ((FullEnsemble.fullRv64imEnsemble (sourceTrace example).programLength
        (sourceTrace example).program).ensemble.allTables.get
          ⟨index, bound⟩).rawWidth = 17 := by
    rw [source]
    exact hw
  change index < 18 at bound
  interval_cases index
  all_goals first
    | exact source.symm
    | cases width

private theorem historical_mem_source (example : Example) (table : Table FGL)
    (ht : table ∈ (sourceTrace example).witness.allTables)
    (hc : (historicalTable table).component = Mem.Legacy457.componentWithDualMemBus) :
    table.component = Mem.componentWithDualMemBus := by
  apply source_mem_component_of_width example table ht
  rw [← historicalTable_rawWidth table, hc] <;> rfl

/-- Full ordered interaction lists, including zero-weight entries. -/
theorem witness_interactionsWith (example : Example) (channel : RawChannel FGL) :
    (witness example).interactionsWith channel =
      (sourceTrace example).witness.interactionsWith channel := by
  simp only [EnsembleWitness.interactionsWith, witness_allTables, List.flatMap_map,
    Table.interactionsWith, historicalTable_table, historicalTable_operations,
    historicalTable_environment]

theorem witness_constraints (example : Example) : (witness example).Constraints := by
  intro table ht
  rw [witness_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  simpa only [Table.Constraints, historicalTable_table, historicalTable_operations,
    historicalTable_environment] using (sourceTrace example).constraints_hold source hs

theorem witness_balancedChannels (example : Example) : (witness example).BalancedChannels := by
  intro channel hc
  have sourceChannel : channel ∈
      (FullEnsemble.fullRv64imEnsemble (sourceTrace example).programLength
        (sourceTrace example).program).ensemble.channels := hc
  have balanced := (sourceTrace example).channels_balanced channel sourceChannel
  change BalancedInteractions ((witness example).interactionsWith channel)
  rw [witness_interactionsWith]
  exact balanced

theorem witness_cyclic (example : Example) :
    (witness example).CyclicSuccessorTransitionConstraints := by
  intro table ht
  rw [witness_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  intro index
  simpa only [historicalTable_cyclic, historicalTable_environmentAt,
    historicalTable_successorEnvironment] using
    (sourceTrace example).cyclic_successor_transitions_hold source hs
      ⟨index.val, by simpa only [historicalTable_length] using index.isLt⟩

/-- Exact original two raw rows/data, with only the historical component identity. -/
private def historicalSdLdMemTable : Table FGL where
  component := Mem.Legacy457.componentWithDualMemBus
  rawRows := sdLdMemTable.rawRows
  data := sdLdMemTable.data
  raw_uniform_width := sdLdMemTable.raw_uniform_width
  fixed_domain := sdLdMemTable.fixed_domain

@[simp] private theorem historicalSdLdMemTable_length :
    historicalSdLdMemTable.length = 2 := rfl

@[simp] private theorem historicalSdLdMemTable_memRowAt_zero :
    memRowFromEnvironment (historicalSdLdMemTable.environmentAt ⟨0, by simp⟩) = sdMemRow :=
  sdLdMemTable_memRowAt_zero

@[simp] private theorem historicalSdLdMemTable_memRowAt_one :
    memRowFromEnvironment (historicalSdLdMemTable.environmentAt ⟨1, by simp⟩) = ldMemRow :=
  sdLdMemTable_memRowAt_one

private def sdLdMemSegmentColumns : ZiskFv.Airs.Mem.SegmentColumns FGL where
  segment_id := 0
  is_first_segment := 1
  is_last_segment := 1
  previous_segment_value_0 := 0
  previous_segment_value_1 := 0
  previous_segment_step := 0
  previous_segment_addr := 335544320
  segment_last_value_0 := 42
  segment_last_value_1 := 0
  segment_last_step := 22
  segment_last_addr := 335544321
  distance_base_0 := 0
  distance_base_1 := 0
  distance_end_0 := 65534
  distance_end_1 := 1023
  segment_l1 := fun row => memFixedColumns.fixedAt MemFixedColumn.segmentL1 row

private def sdLdMemPermutationColumns : ZiskFv.AirsClean.Mem.Legacy457.PermutationColumns FGL where
  std_alpha := 0
  std_gamma := 1
  l1 := fun row => memFixedColumns.fixedAt MemFixedColumn.l1 row
  im_direct_0 := 1537228672451215360
  im_direct_1 := 0
  im_direct_2 := 10110234730352224099
  im_direct_3 := 10110234730352224099
  im_direct_4 := 10110234730352224099
  im_direct_5 := 10110234730352224099

private theorem sdLdMemSegmentColumns_source :
    memSegmentColumnsOfProverDataAndFixed sdLdMemData
      (fun row => memFixedColumns.fixedAt MemFixedColumn.segmentL1 row) =
      sdLdMemSegmentColumns := by
  simp [sdLdMemSegmentColumns]

private theorem sdLdMemPermutationColumns_source :
    Mem.Legacy457.permutationColumnsOfProverDataAndFixed sdLdMemData
      (fun row => memFixedColumns.fixedAt MemFixedColumn.l1 row) =
      sdLdMemPermutationColumns := by
  simp [sdLdMemPermutationColumns, Mem.Legacy457.permutationColumnsOfProverDataAndFixed, proverDataScalar, sdLdMemData]

private theorem historicalSdLdMemTable_rangeBridge_zero :
    memRangeSidecarBridge (historicalSdLdMemTable.environmentAt ⟨0, by simp⟩) := by
  exact ⟨eval_memDistanceBase0Expr_materialize 0 sdLdMemData sdMemRow,
    eval_memDistanceBase1Expr_materialize 0 sdLdMemData sdMemRow,
    eval_memDistanceEnd0Expr_materialize 0 sdLdMemData sdMemRow,
    eval_memDistanceEnd1Expr_materialize 0 sdLdMemData sdMemRow⟩

private theorem historicalSdLdMemTable_rangeBridge_one :
    memRangeSidecarBridge (historicalSdLdMemTable.environmentAt ⟨1, by simp⟩) := by
  exact ⟨eval_memDistanceBase0Expr_materialize 1 sdLdMemData ldMemRow,
    eval_memDistanceBase1Expr_materialize 1 sdLdMemData ldMemRow,
    eval_memDistanceEnd0Expr_materialize 1 sdLdMemData ldMemRow,
    eval_memDistanceEnd1Expr_materialize 1 sdLdMemData ldMemRow⟩

/-- The two real Mem rows satisfy every generated continuity, range-source,
and permutation equation. Row zero uses the component's saturated
predecessor; row one uses the preceding store row. -/
private theorem historicalSdLdMemTable_transitions : historicalSdLdMemTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_index_lt : index.val < 2 := by
    simpa only [historicalSdLdMemTable_length] using index.isLt
  interval_cases h : index.val
  · have h_eq : index = ⟨0, by simp⟩ := Fin.ext (by omega)
    subst index
    let previous := historicalSdLdMemTable.previousEnvironment ⟨0, by simp⟩
    let current := historicalSdLdMemTable.environmentAt ⟨0, by simp⟩
    have h_current : memRowFromEnvironment current = sdMemRow := by
      exact historicalSdLdMemTable_memRowAt_zero
    have h_previous :
        memRowFromEnvironment previous = sdMemRow := by
      dsimp [previous]
      simpa only [Table.previousEnvironment, Nat.zero_sub] using h_current
    have h_data : current.data = sdLdMemData := by rfl
    have h_range : memRangeSidecarBridge current := by
      exact historicalSdLdMemTable_rangeBridge_zero
    change Mem.Legacy457.generatedTransition memFixedColumns 0 previous current
    simp only [Mem.Legacy457.generatedTransition, h_data, sdLdMemSegmentColumns_source,
      sdLdMemPermutationColumns_source]
    refine ⟨?_, ?_, h_range⟩
    · norm_num [ZiskFv.Airs.Mem.segmentResidualEveryRow, memWindow, h_current,
        h_previous, sdLdMemSegmentColumns, ZiskFv.Airs.Mem.previous_row_step,
        ZiskFv.Airs.Mem.delta_addr, ZiskFv.Airs.Mem.segment_previous_addr,
        ZiskFv.Airs.Mem.delta_step, ZiskFv.Airs.Mem.segment_previous_value_0,
        ZiskFv.Airs.Mem.segment_previous_value_1, sdMemRow, memRowOf,
        memReadSameAddrOf, memValueOf]
    · norm_num [ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row, memWindow, h_current,
        h_previous, h_data, sdLdMemPermutationColumns, ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_1,
        ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_step, ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_0,
        ZiskFv.AirsClean.Mem.Legacy457.gsum_primary_mem, ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_mem,
        sdLdMemSegmentColumns, ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_0, ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_1,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_base_0,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_base_1,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_end_0,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_end_1,
        ZiskFv.AirsClean.Mem.Legacy457.gsum_accumulator_delta, sdMemRow, memRowOf,
        memReadSameAddrOf, memValueOf] ; decide
  · have h_eq : index = ⟨1, by simp⟩ := Fin.ext (by omega)
    subst index
    let previous := historicalSdLdMemTable.previousEnvironment ⟨1, by simp⟩
    let current := historicalSdLdMemTable.environmentAt ⟨1, by simp⟩
    have h_current : memRowFromEnvironment current = ldMemRow := by
      exact historicalSdLdMemTable_memRowAt_one
    have h_previous :
        memRowFromEnvironment previous = sdMemRow := by
      dsimp [previous]
      simpa only [Table.previousEnvironment] using historicalSdLdMemTable_memRowAt_zero
    have h_data : current.data = sdLdMemData := by rfl
    have h_range : memRangeSidecarBridge current := by
      exact historicalSdLdMemTable_rangeBridge_one
    change Mem.Legacy457.generatedTransition memFixedColumns 1 previous current
    simp only [Mem.Legacy457.generatedTransition, h_data, sdLdMemSegmentColumns_source,
      sdLdMemPermutationColumns_source]
    refine ⟨?_, ?_, h_range⟩
    · norm_num [ZiskFv.Airs.Mem.segmentResidualEveryRow, memWindow, h_current,
        h_previous, sdLdMemSegmentColumns, ZiskFv.Airs.Mem.previous_row_step,
        ZiskFv.Airs.Mem.delta_addr, ZiskFv.Airs.Mem.segment_previous_addr,
        ZiskFv.Airs.Mem.delta_step, ZiskFv.Airs.Mem.segment_previous_value_0,
        ZiskFv.Airs.Mem.segment_previous_value_1, sdMemRow, ldMemRow, memRowOf,
        memReadSameAddrOf, memValueOf]
    · norm_num [ZiskFv.AirsClean.Mem.Legacy457.permutation_every_row, memWindow, h_current,
        h_previous, h_data, sdLdMemPermutationColumns, ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_1,
        ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_step, ZiskFv.AirsClean.Mem.Legacy457.gsum_increment_0,
        ZiskFv.AirsClean.Mem.Legacy457.gsum_primary_mem, ZiskFv.AirsClean.Mem.Legacy457.gsum_dual_mem,
        sdLdMemSegmentColumns, ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_0, ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_1,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_base_0,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_base_1,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_end_0,
        ZiskFv.AirsClean.Mem.Legacy457.direct_gsum_distance_end_1,
        ZiskFv.AirsClean.Mem.Legacy457.gsum_accumulator_delta, sdMemRow, ldMemRow, memRowOf,
        memReadSameAddrOf, memValueOf] ; decide

/-- Exact physical-source provenance, including every fixed slot at every
row, not merely equality of decoded replay entries or active provider keys. -/
theorem witness_sources (example : Example) :
    (witness example).tables.map
      (fun table => (table.rawRows, table.data, fun slot row => table.fixedAt slot row)) =
    (sourceTrace example).witness.tables.map
      (fun table => (table.rawRows, table.data, fun slot row => table.fixedAt slot row)) := by
  simp only [witness, List.map_map, Function.comp_def, historicalTable_rawRows,
    historicalTable_data, historicalTable_fixedAt]

private theorem singleAdd_source_no_mem :
    ¬ ZiskFv.Compliance.MutableMemPresent (sourceTrace .singleAdd).witness := by
  intro ⟨table, ht, hc, hn⟩
  change table ∈ SingleAddWitness.singleAddWitness.allTables at ht
  simp only [EnsembleWitness.allTables, SingleAddWitness.singleAddWitness,
    SingleAddWitness.singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (have impossible := congrArg (fun c : Component FGL => c.rawWidth) hc
       norm_num at impossible
       done)
    | (change (0 : Nat) < 0 at hn
       omega)

private theorem emptyCases_no_mem (example : Example) (hne : example ≠ .sdLd) :
    ¬ ZiskFv.Compliance.MutableMemPresent (sourceTrace example).witness := by
  cases example with
  | singleAdd => exact singleAdd_source_no_mem
  | addSpin => exact AddSpinWitness.addSpinWitness_not_mutableMemPresent
  | addAddiSpin => exact AddAddiSpinWitness.addAddiSpinWitness_not_mutableMemPresent
  | addFaithful => exact AddFaithfulPaddedWitness.addFaithfulWitness_not_mutableMemPresent
  | jalr => exact JalrSpinWitness.jalrWitness_not_mutableMemPresent
  | sdLd => exact False.elim (hne rfl)
  | divSpin => exact DivSpinWitness.divSpinWitness_not_mutableMemPresent

/-- Old D1 is proved for the seven fixed cases. The sole nonempty Mem case
uses the independent original-numeric proof above; no new-domain Mem D1 is
used in this branch. All other components are the exact original objects. -/
theorem witness_transitions (example : Example) : (witness example).TransitionConstraints := by
  classical
  intro table ht
  rw [witness_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  by_cases hm : source.component = Mem.componentWithDualMemBus
  · by_cases he : example = .sdLd
    · subst example
      have guard : ZiskFv.Compliance.MutableMemPresent
          SdLdSpinWitness.sdLdWitness := by
        refine ⟨SdLdSpinWitness.sdLdTableWithData sdLdMemTable, ?_, rfl, ?_⟩
        · simp [EnsembleWitness.allTables, SdLdSpinWitness.sdLdWitness,
            SdLdSpinWitness.sdLdTables]
        · norm_num [SdLdSpinWitness.sdLdTableWithData, sdLdMemTable,
            memRowsTable, sdLdMemRows]
      have hsource : source = SdLdSpinWitness.sdLdTableWithData sdLdMemTable :=
        (sourceTrace .sdLd).mem_replay_source_covers guard source hs hm
      subst source
      have htable :
          historicalTable (SdLdSpinWitness.sdLdTableWithData sdLdMemTable) =
            historicalSdLdMemTable := by
        simp only [historicalTable, dif_pos (show
          (SdLdSpinWitness.sdLdTableWithData sdLdMemTable).component =
            Mem.componentWithDualMemBus from rfl)]
        rfl
      rw [htable]
      exact historicalSdLdMemTable_transitions
    · intro index
      apply False.elim
      apply emptyCases_no_mem example he
      refine ⟨source, hs, hm, ?_⟩
      rw [Table.table_length]
      have bound := index.isLt
      rw [historicalTable_length] at bound
      omega
  · rw [historicalTable_of_ne source hm]
    exact (sourceTrace example).transitions_hold source hs

private theorem historical_presence_source (example : Example)
    (guard : ZiskFv.Compliance.Legacy457.MutableMemPresent (witness example)) :
    ZiskFv.Compliance.MutableMemPresent (sourceTrace example).witness := by
  rcases guard with ⟨table, ht, hc, hn⟩
  rw [witness_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  exact ⟨source, hs, historical_mem_source example source hs hc,
    by simpa only [historicalTable_table] using hn⟩

private def selectedHistoricalTable (example : Example)
    (guard : ZiskFv.Compliance.Legacy457.MutableMemPresent (witness example)) :
    { table : Table FGL //
      table ∈ (witness example).allTables ∧
        table.component = Mem.Legacy457.componentWithDualMemBus ∧
        0 < table.table.length } :=
  let selected := (sourceTrace example).mem_replay_table
    (historical_presence_source example guard)
  ⟨historicalTable selected.1,
    by
      rw [witness_allTables]
      exact List.mem_map.mpr ⟨selected.1, selected.2.1, rfl⟩,
    historicalTable_mem_component selected.1 selected.2.2.1,
    by simpa only [historicalTable_table] using selected.2.2.2⟩

private theorem selectedHistoricalTable_covers (example : Example)
    (guard : ZiskFv.Compliance.Legacy457.MutableMemPresent (witness example))
    (table : Table FGL) (ht : table ∈ (witness example).allTables)
    (hc : table.component = Mem.Legacy457.componentWithDualMemBus) :
    table = (selectedHistoricalTable example guard).1 := by
  rw [witness_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  have sourceMem := historical_mem_source example source hs hc
  have covered := (sourceTrace example).mem_replay_source_covers
    (historical_presence_source example guard) source hs sourceMem
  exact congrArg historicalTable covered

private theorem historical_main_height {n : Nat} (example : Example)
    (height : ∀ table ∈ (sourceTrace example).witness.allTables,
      table.component = Main.componentWithRomMemAndOpBus
        (sourceTrace example).programLength (sourceTrace example).program →
          ∀ index : Fin n, index.val < table.table.length) :
    ∀ table ∈ (witness example).allTables,
      table.component = Main.componentWithRomMemAndOpBus
        (sourceTrace example).programLength (sourceTrace example).program →
          ∀ index : Fin n, index.val < table.table.length := by
  classical
  intro table ht hc index
  rw [witness_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  by_cases hm : source.component = Mem.componentWithDualMemBus
  · have impossible := congrArg (fun c : Component FGL => c.rawWidth) hc
    rw [historicalTable_mem_component source hm] at impossible
    change (17 : Nat) = 41 at impossible
    omega
  · rw [historicalTable_of_ne source hm] at hc ⊢
    exact height source hs hc index

private def accepted (example : Example) :
    ZiskFv.Compliance.Legacy457.AcceptedZiskTrace (instructionCount example) where
  programLength := (sourceTrace example).programLength
  program := (sourceTrace example).program
  witness := witness example
  constraints_hold := witness_constraints example
  channels_balanced := witness_balancedChannels example
  mem_replay_table := selectedHistoricalTable example
  mem_replay_source_covers := selectedHistoricalTable_covers example
  transitions_hold := witness_transitions example
  cyclic_successor_transitions_hold := witness_cyclic example
  main_height := historical_main_height example (sourceTrace example).main_height

def singleAddAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 1 :=
  accepted .singleAdd

def addSpinAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 2 :=
  accepted .addSpin

def addAddiSpinAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 3 :=
  accepted .addAddiSpin

def addFaithfulAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 1 :=
  accepted .addFaithful

def jalrAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 2 :=
  accepted .jalr

def sdLdAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 7 :=
  accepted .sdLd

def divSpinAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 4 :=
  accepted .divSpin

/-- The original ADD/JAL committed rows, with the original one-step prefix,
not a shortened raw table or a new numeric acceptance assumption. -/
def addPaddedAcceptedTrace : ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 1 where
  programLength := (sourceTrace .addSpin).programLength
  program := (sourceTrace .addSpin).program
  witness := witness .addSpin
  constraints_hold := witness_constraints .addSpin
  channels_balanced := witness_balancedChannels .addSpin
  mem_replay_table := selectedHistoricalTable .addSpin
  mem_replay_source_covers := selectedHistoricalTable_covers .addSpin
  transitions_hold := witness_transitions .addSpin
  cyclic_successor_transitions_hold := witness_cyclic .addSpin
  main_height := historical_main_height .addSpin
    AddSpinWitness.addSpinWitness_main_height_prefix_one

theorem addPaddedAcceptedTrace_same_committed_witness :
    addPaddedAcceptedTrace.witness = addSpinAcceptedTrace.witness := rfl

theorem singleAdd_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 1) :=
  ⟨singleAddAcceptedTrace⟩

theorem addSpin_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 2) :=
  ⟨addSpinAcceptedTrace⟩

theorem addAddiSpin_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 3) :=
  ⟨addAddiSpinAcceptedTrace⟩

theorem addFaithful_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 1) :=
  ⟨addFaithfulAcceptedTrace⟩

theorem jalr_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 2) :=
  ⟨jalrAcceptedTrace⟩

theorem sdLd_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 7) :=
  ⟨sdLdAcceptedTrace⟩

theorem divSpin_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 4) :=
  ⟨divSpinAcceptedTrace⟩

theorem addPadded_nonvacuous : Nonempty (ZiskFv.Compliance.Legacy457.AcceptedZiskTrace 1) :=
  ⟨addPaddedAcceptedTrace⟩

end
end ZiskFv.Compliance.Legacy457.ConcreteOldWorlds
