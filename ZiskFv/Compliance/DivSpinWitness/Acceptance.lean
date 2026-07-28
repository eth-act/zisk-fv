import ZiskFv.Compliance.DivSpinWitness.Balance

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option Elab.async false

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.DivSpinWitness

private theorem not_divSpin_main_component_of_name_ne
    {component : Component FGL}
    (h_name : component.circuit.name ≠
      (componentWithRomMemAndOpBus 4 divSpinProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 4 divSpinProgram) : False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem not_divSpin_main_component_of_width_ne
    {component : Component FGL}
    (h_width : component.width ≠
      (componentWithRomMemAndOpBus 4 divSpinProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 4 divSpinProgram) : False :=
  h_width (congrArg Component.width h_component)

private theorem not_divSpin_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name : component.circuit.name ≠
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component : component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) : False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem divSpinWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ divSpinWitness.allTables)
    (h_component :
      table.component = componentWithRomMemAndOpBus 4 divSpinProgram) :
    table = divSpinMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_divSpin_main_component_of_width_ne (by decide) h_component
  · rw [divSpinWitness_tables] at h_table
    simp [divSpinTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exfalso
        exact not_divSpin_main_component_of_name_ne (by decide) h_component

private theorem divSpinWitness_mutable_mem_component_tables_empty
    (table : Table FGL) (h_table : table ∈ divSpinWitness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    exact not_divSpin_mutable_mem_component_of_name_ne (by decide) h_component
  · rw [divSpinWitness_tables] at h_table
    simp [divSpinTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_divSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exact emptyComponentTable_table _
    · exfalso
      exact not_divSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table _
    · exfalso
      exact not_divSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_divSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_divSpin_mutable_mem_component_of_name_ne (by decide) h_component

theorem divSpinWitness_not_mutableMemPresent :
    ¬ MutableMemPresent divSpinWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    divSpinWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem divSpinWitness_main_height :
    ∀ table ∈ divSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 4 divSpinProgram →
        ∀ i : Fin 4, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := divSpinWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;> norm_num [divSpinMainTable, mainRowsTable, divSpinMainRows]

def divSpinAcceptedTrace : AcceptedZiskTrace 4 where
  programLength := 4
  program := divSpinProgram
  witness := divSpinWitness
  constraints_hold := divSpinWitness_constraints
  channels_balanced := divSpinWitness_balancedChannels
  mem_replay_table := fun h => absurd h divSpinWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h divSpinWitness_not_mutableMemPresent
  transitions_hold := divSpinWitness_transitions
  cyclic_successor_transitions_hold := divSpinWitness_cyclicSuccessorTransitions
  main_height := divSpinWitness_main_height

theorem divSpinAcceptedTrace_mainTable_eq :
    divSpinAcceptedTrace.mainTable = divSpinMainTable := by
  exact divSpinWitness_main_component_cases
    (by simpa [divSpinAcceptedTrace] using divSpinAcceptedTrace.mainTable_mem)
    (by simpa [divSpinAcceptedTrace] using divSpinAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.DivSpinWitness
