import Source458DomainComparison.Accepted18

/-!
# Same-data erasure of the retired scalar Mem acceptance restriction

Only the component identity of the historical Mem table changes. Raw rows,
prover data, effective fixed rows, operations, and the complete ordered channel
streams are preserved. In particular the balance transport retains the original
interaction-length bound, not just the zero-sum consequence. This construction
has no inverse reconstructing the retired scalar equations.
-/

namespace ZiskFv.AirsClean.FullEnsemble.MemDomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

abbrev OldWitness (p : Nat) (program : Program p) :=
  EnsembleWitness (Legacy457.fullRv64imEnsemble p program).ensemble

abbrev NewWitness (p : Nat) (program : Program p) :=
  EnsembleWitness (fullRv64imEnsemble p program).ensemble

variable {p : Nat} {program : Program p}

noncomputable section

/-- Replace only the historical Mem component, retaining the actual original
raw buffers and data. The unchanged width/fixed schema justify the carrier. -/
def retargetTable (table : Table FGL) : Table FGL := by
  classical
  exact if h : table.component = Mem.Legacy457.componentWithDualMemBus then
    { component := Mem.componentWithDualMemBus
      rawRows := table.rawRows
      data := table.data
      raw_uniform_width := by
        intro row hr
        have width := table.raw_uniform_width row hr
        simpa only [h] using width
      fixed_domain := by
        intro columns hc
        have domain := table.fixed_domain
        rw [h] at domain
        exact domain columns hc }
    else table

theorem retargetTable_of_ne (table : Table FGL)
    (h : table.component ≠ Mem.Legacy457.componentWithDualMemBus) :
    retargetTable table = table := by
  classical
  simp only [retargetTable, dif_neg h]

theorem retargetTable_mem_component (table : Table FGL)
    (h : table.component = Mem.Legacy457.componentWithDualMemBus) :
    (retargetTable table).component = Mem.componentWithDualMemBus := by
  classical
  simp only [retargetTable, dif_pos h]

@[simp] theorem retargetTable_rawRows (table : Table FGL) :
    (retargetTable table).rawRows = table.rawRows := by
  classical
  unfold retargetTable
  split <;> rfl

@[simp] theorem retargetTable_data (table : Table FGL) :
    (retargetTable table).data = table.data := by
  classical
  unfold retargetTable
  split <;> rfl

@[simp] theorem retargetTable_length (table : Table FGL) :
    (retargetTable table).length = table.length := by
  simp only [Table.length, retargetTable_rawRows]

@[simp] theorem retargetTable_rawWidth (table : Table FGL) :
    (retargetTable table).component.rawWidth = table.component.rawWidth := by
  classical
  unfold retargetTable
  split
  · rename_i h
    rw [h] <;> rfl
  · rfl

@[simp] theorem retargetTable_table (table : Table FGL) :
    (retargetTable table).table = table.table := by
  classical
  by_cases h : table.component = Mem.Legacy457.componentWithDualMemBus
  · simp only [retargetTable, dif_pos h, Table.table, h] <;> rfl
  · rw [retargetTable_of_ne table h]

@[simp] theorem retargetTable_fixedAt (table : Table FGL) (slot row : Nat) :
    (retargetTable table).fixedAt slot row = table.fixedAt slot row := by
  classical
  by_cases h : table.component = Mem.Legacy457.componentWithDualMemBus
  · simp only [retargetTable, dif_pos h, Table.fixedAt, h] <;> rfl
  · rw [retargetTable_of_ne table h]

@[simp] theorem retargetTable_materializeRow (table : Table FGL)
    (index : Nat) (raw : Array FGL) :
    (retargetTable table).materializeRow index raw = table.materializeRow index raw := by
  classical
  by_cases h : table.component = Mem.Legacy457.componentWithDualMemBus
  · simp only [retargetTable, dif_pos h, Table.materializeRow, h] <;> rfl
  · rw [retargetTable_of_ne table h]

@[simp] theorem retargetTable_environment (table : Table FGL) (row : Array FGL) :
    (retargetTable table).environment row = table.environment row := by
  simp only [Table.environment, retargetTable_data]

@[simp] theorem retargetTable_environmentAt (table : Table FGL)
    (index : Fin (retargetTable table).length) :
    (retargetTable table).environmentAt index =
      table.environmentAt ⟨index.val, by simpa only [retargetTable_length] using index.isLt⟩ := by
  simp only [Table.environmentAt, retargetTable_environment, retargetTable_table]

@[simp] theorem retargetTable_previousEnvironment (table : Table FGL)
    (index : Fin (retargetTable table).length) :
    (retargetTable table).previousEnvironment index =
      table.previousEnvironment
        ⟨index.val, by simpa only [retargetTable_length] using index.isLt⟩ := by
  simp only [Table.previousEnvironment, retargetTable_environmentAt]

@[simp] theorem retargetTable_successorEnvironment (table : Table FGL)
    (index : Fin (retargetTable table).length) :
    (retargetTable table).successorEnvironment index =
      table.successorEnvironment
        ⟨index.val, by simpa only [retargetTable_length] using index.isLt⟩ := by
  simp only [Table.successorEnvironment, Table.successorIndex,
    retargetTable_environmentAt, retargetTable_length]

@[simp] theorem retargetTable_operations (table : Table FGL) :
    (retargetTable table).component.operations = table.component.operations := by
  classical
  unfold retargetTable
  split
  · rename_i h
    rw [h] <;> rfl
  · rfl

@[simp] theorem retargetTable_cyclicTransition (table : Table FGL) :
    (retargetTable table).component.cyclicSuccessorTransition =
      table.component.cyclicSuccessorTransition := by
  classical
  unfold retargetTable
  split
  · rename_i h
    rw [h] <;> rfl
  · rfl

theorem retargetTable_constraints (table : Table FGL) (h : table.Constraints) :
    (retargetTable table).Constraints := by
  simpa only [Table.Constraints, retargetTable_table,
    retargetTable_operations, retargetTable_environment] using h

/-- The only changed verifier predicate is discharged by projecting the
historical D1 evidence; no corrected transition certificate is supplied. -/
theorem retargetTable_transitions (table : Table FGL) (h : table.TransitionConstraints) :
    (retargetTable table).TransitionConstraints := by
  classical
  by_cases hc : table.component = Mem.Legacy457.componentWithDualMemBus
  · intro index
    let oldIndex : Fin table.length :=
      ⟨index.val, by simpa only [retargetTable_length] using index.isLt⟩
    have oldTransition := h oldIndex
    rw [hc] at oldTransition
    have corrected := Mem.Legacy457.generatedTransition_implies_current
      Mem.memFixedColumns index.val (table.previousEnvironment oldIndex)
      (table.environmentAt oldIndex) oldTransition
    simpa only [retargetTable_mem_component table hc,
      Mem.componentWithDualMemBus, retargetTable_previousEnvironment,
      retargetTable_environmentAt, oldIndex] using corrected
  · simpa only [retargetTable_of_ne table hc] using h

theorem retargetTable_cyclic (table : Table FGL)
    (h : table.CyclicSuccessorTransitionConstraints) :
    (retargetTable table).CyclicSuccessorTransitionConstraints := by
  intro index
  simpa only [retargetTable_cyclicTransition, retargetTable_environmentAt,
    retargetTable_successorEnvironment] using
    h ⟨index.val, by simpa only [retargetTable_length] using index.isLt⟩

@[simp] theorem retargetTable_interactions (table : Table FGL) :
    (retargetTable table).interactions = table.interactions := by
  simp only [Table.interactions, retargetTable_table,
    retargetTable_operations, retargetTable_environment]

@[simp] theorem retargetTable_interactionsWith (table : Table FGL)
    (channel : RawChannel FGL) :
    (retargetTable table).interactionsWith channel = table.interactionsWith channel := by
  simp only [Table.interactionsWith, retargetTable_table,
    retargetTable_operations, retargetTable_environment]

private theorem retargetTable_component_of_width (table : Table FGL)
    (component : Component FGL) (hc : table.component = component)
    (hw : component.rawWidth ≠ 17) :
    (retargetTable table).component = component := by
  apply Eq.trans (congrArg Table.component (retargetTable_of_ne table ?_)) hc
  intro hm
  apply hw
  rw [← hc, hm] <;> rfl

/-- The original seventeen physical tables stay in the same positions; only
physical index6 (allTables index7) is the retargeted Mem table. -/
def eraseLegacyMem (old : OldWitness p program) : NewWitness p program where
  tables := old.tables.map retargetTable
  data := old.data
  publicInput := old.publicInput
  same_length := by
    rw [List.length_map, ← old.same_length] <;> rfl
  same_circuits := by
    intro index hi
    have oldBound : index < (Legacy457.fullRv64imEnsemble p program).ensemble.tables.length := by
      change index < 17
      change index < 17 at hi
      exact hi
    rw [List.getElem_map]
    have bound : index < 17 := by change index < 17 at hi; exact hi
    interval_cases index
    all_goals first
      | exact (retargetTable_mem_component _ (old.same_circuits _ oldBound).symm).symm
      | (symm
         apply retargetTable_component_of_width _ _ (old.same_circuits _ oldBound).symm
         decide)
  same_data := by
    intro table ht
    rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
    rw [retargetTable_data]
    exact old.same_data source hs

@[simp] theorem eraseLegacyMem_data (old : OldWitness p program) :
    (eraseLegacyMem old).data = old.data := rfl

@[simp] theorem eraseLegacyMem_publicInput (old : OldWitness p program) :
    (eraseLegacyMem old).publicInput = old.publicInput := rfl

theorem eraseLegacyMem_verifierTable (old : OldWitness p program) :
    (eraseLegacyMem old).verifierTable = old.verifierTable := by
  apply Ensemble.verifierTable_ext <;> rfl

private theorem retargetTable_verifierTable (old : OldWitness p program) :
    retargetTable old.verifierTable = old.verifierTable := by
  apply retargetTable_of_ne
  intro h
  have hw := congrArg (fun component : Component FGL => component.rawWidth) h
  change (0 : Nat) = 17 at hw
  omega

theorem eraseLegacyMem_allTables (old : OldWitness p program) :
    (eraseLegacyMem old).allTables = old.allTables.map retargetTable := by
  simp only [EnsembleWitness.allTables, List.map_cons,
    retargetTable_verifierTable, eraseLegacyMem_verifierTable] <;> rfl

theorem nonMem_table_preserved (old : OldWitness p program) (table : Table FGL)
    (ht : table ∈ old.allTables)
    (h : table.component ≠ Mem.Legacy457.componentWithDualMemBus) :
    table ∈ (eraseLegacyMem old).allTables := by
  rw [eraseLegacyMem_allTables]
  exact List.mem_map.mpr ⟨table, ht, retargetTable_of_ne table h⟩

/-- All historical width17 tables have the historical Mem component. This is
roster classification, including empty tables, not a native identity premise. -/
theorem old_mem_component_of_width (old : OldWitness p program) (table : Table FGL)
    (ht : table ∈ old.allTables) (hw : table.component.rawWidth = 17) :
    table.component = Mem.Legacy457.componentWithDualMemBus := by
  have hc := EnsembleWitness.mem_allTables_component_of_mem_allTables ht
  simp only [Legacy457.fullRv64imEnsemble, Legacy457.fullRv64imSoundEnsemble,
    circuit_norm, Ensemble.allTables] at hc
  rcases hc with
    hc | hc | hc | hc | hc | hc | hc | hc | hc |
    hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals first
    | exact hc
    | (have impossible := congrArg (fun component : Component FGL => component.rawWidth) hc
       rw [hw] at impossible
       norm_num at impossible)

theorem eraseLegacyMem_constraints (old : OldWitness p program)
    (h : old.Constraints) : (eraseLegacyMem old).Constraints := by
  intro table ht
  rw [eraseLegacyMem_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  exact retargetTable_constraints source (h source hs)

theorem eraseLegacyMem_transitions (old : OldWitness p program)
    (h : old.TransitionConstraints) : (eraseLegacyMem old).TransitionConstraints := by
  intro table ht
  rw [eraseLegacyMem_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  exact retargetTable_transitions source (h source hs)

theorem eraseLegacyMem_cyclic (old : OldWitness p program)
    (h : old.CyclicSuccessorTransitionConstraints) :
    (eraseLegacyMem old).CyclicSuccessorTransitionConstraints := by
  intro table ht
  rw [eraseLegacyMem_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  exact retargetTable_cyclic source (h source hs)

/-- Exact list equality preserves messages, multiplicities, zero weights,
within-table order, between-table order, and the length-overflow obligation. -/
theorem eraseLegacyMem_interactionsWith (old : OldWitness p program)
    (channel : RawChannel FGL) :
    (eraseLegacyMem old).interactionsWith channel = old.interactionsWith channel := by
  simp only [EnsembleWitness.interactionsWith, eraseLegacyMem_allTables,
    List.flatMap_map, retargetTable_interactionsWith]

theorem eraseLegacyMem_interactions (old : OldWitness p program) :
    (eraseLegacyMem old).interactions = old.interactions := by
  simp only [EnsembleWitness.interactions, eraseLegacyMem_allTables,
    List.flatMap_map, retargetTable_interactions]

theorem eraseLegacyMem_balancedChannels (old : OldWitness p program)
    (h : old.BalancedChannels) : (eraseLegacyMem old).BalancedChannels := by
  intro channel hc
  have oldChannel : channel ∈
      (Legacy457.fullRv64imEnsemble p program).ensemble.channels := hc
  have balanced := h channel oldChannel
  change BalancedInteractions ((eraseLegacyMem old).interactionsWith channel)
  rw [eraseLegacyMem_interactionsWith]
  exact balanced

end
end ZiskFv.AirsClean.FullEnsemble.MemDomainComparison
