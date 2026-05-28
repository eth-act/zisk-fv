import ZiskFv.AirsClean.MemFamily.Ensemble

/-!
# Memory-family memory-bus balance projections (Phase T4.2)

Bridge lemmas that expose the Clean `memBusEnsemble`'s balanced
`MemBusChannel` fact in the form needed by the later memory-bus
balance proofs. Mirrors the C7 `BinaryFamily/Balance.lean` pattern
but for the memory family (Main consumer + Mem provider) instead of
the operation-bus family.

## T4.2 status

This file holds the foundational classification + verifier-empty
lemmas. The full balance projection (active Main mem-bus interaction
→ concrete Mem provider row + `matches_memory_entry`) is built
incrementally as subsequent commits stack on this base.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemFamily

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- The concrete component list in the memory-family ensemble. Kept as a
    small standalone lemma because dependent component equalities are
    fragile when case-split in larger balance proofs. -/
theorem component_mem_memFamily_cases
    {length : ℕ} {program : Program length}
    {component : Component FGL}
    (h_mem : component ∈ (memBusEnsemble length program).ensemble.allTables) :
    component = (memBusEnsemble length program).ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.MemAlignReadByte.component
      ∨ component = ZiskFv.AirsClean.MemAlignByte.component
      ∨ component = ZiskFv.AirsClean.MemAlign.component
      ∨ component = ZiskFv.AirsClean.Mem.componentWithMemBus
      ∨ component =
        ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program := by
  simp [memBusEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
    at h_mem
  rcases h_mem with h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_memAlign)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_mem))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main))))
  · cases h_empty

/-- The memory-family verifier table is the empty verifier component, so it
    cannot contribute memory-bus interactions. -/
theorem verifierTable_interactionsWith_memBus_nil
    (length : ℕ) (program : Program length) :
    (memBusEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      MemBusChannel.toRaw = [] := by
  simp [memBusEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- Project the memory-family ensemble's `BalancedChannels` hypothesis to
    the concrete memory-bus interaction list. -/
theorem memBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (memBusEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith MemBusChannel.toRaw) := by
  have h := h_balanced MemBusChannel.toRaw (by
    change MemBusChannel.toRaw ∈ [MemBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Clean balance replacement shape for the old memory-bus permutation
    axiom: an active Main-side consumer interaction (`mult = -1`) has a
    same-message nonzero counterpart that is not another pull. -/
theorem exists_matching_nonzero_nonpull_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (memBusEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith MemBusChannel.toRaw)
    (memBus_balanced_of_witness witness h_balanced)
    mainInteraction h_mem h_active

/-- If a table's memory-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- Row extraction for a Main memory-bus interaction. Main exposes three
    interactions (a, b, c/store), so the result keeps the side disjunction
    explicit. -/
theorem exists_main_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg))
            (ZiskFv.AirsClean.Main.aMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg))
            (ZiskFv.AirsClean.Main.bMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar.rom.store_reg))
            (ZiskFv.AirsClean.Main.cMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program).rowInputVar)).toRaw).eval
            (table.environment row) := by
  have h_interactions :=
    ZiskFv.AirsClean.Main.componentWithRomAndMemBus_interactionsWith_memBus
      length program
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_component, h_interactions] at h_mem
  rcases h_mem with ⟨row, h_row, h_eq | h_eq | h_eq⟩
  · refine ⟨row, h_row, Or.inl ?_⟩
    exact h_eq
  · refine ⟨row, h_row, Or.inr (Or.inl ?_)⟩
    exact h_eq
  · refine ⟨row, h_row, Or.inr (Or.inr ?_)⟩
    exact h_eq

theorem exists_mem_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithMemBus_interactionsWith_memBus
  · exact h_mem

theorem exists_memAlign_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
            - ZiskFv.AirsClean.MemAlign.selAssumeExpr
              ZiskFv.AirsClean.MemAlign.component.rowInputVar)
          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memBus
  · exact h_mem

theorem exists_memAlignByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus
  · exact h_mem

theorem exists_memAlignReadByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus
  · exact h_mem

/-- Component classification for the balanced same-message counterpart.

This intentionally keeps the Main case visible. Excluding Main requires
additional ROM-selector legality (for example, one-hot source/store classes)
that is not currently part of the Clean Main component's row soundness.
Keeping the disjunction explicit prevents laundering that missing fact into a
"provider" theorem. -/
theorem exists_matching_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (memBusEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith MemBusChannel.toRaw
            ∧ (table.component = ZiskFv.AirsClean.MemAlignReadByte.component
              ∨ table.component = ZiskFv.AirsClean.MemAlignByte.component
              ∨ table.component = ZiskFv.AirsClean.MemAlign.component
              ∨ table.component = ZiskFv.AirsClean.Mem.componentWithMemBus
              ∨ table.component =
                  ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_component_mem :
      table.component ∈ (memBusEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_memFamily_cases h_component_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_main
  · have h_nil :
        table.interactionsWith MemBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith MemBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_memBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table,
      h_table, h_mem_table, Or.inl h_marb⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨table, h_table, h_mem_table⟩
  · refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table,
      h_table, h_mem_table, Or.inr (Or.inl h_mab)⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨table, h_table, h_mem_table⟩
  · refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table,
      h_table, h_mem_table, Or.inr (Or.inr (Or.inl h_memAlign))⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨table, h_table, h_mem_table⟩
  · refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table,
      h_table, h_mem_table, Or.inr (Or.inr (Or.inr (Or.inl h_mem)))⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨table, h_table, h_mem_table⟩
  · refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table,
      h_table, h_mem_table, Or.inr (Or.inr (Or.inr (Or.inr h_main)))⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨table, h_table, h_mem_table⟩

end ZiskFv.AirsClean.MemFamily
