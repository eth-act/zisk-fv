import ZiskFv.AirsClean.BinaryFamily.Ensemble

/-!
# Binary-family operation-bus balance projections

Small C7 bridge lemmas that expose the Clean ensemble's balanced
`OpBusChannel` fact in the form needed by the later `matches_entry`
replacement proofs.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.BinaryFamily

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus

/-- The concrete component list in the Binary-family ensemble. Kept as a
    small standalone lemma because dependent component equalities are fragile
    when case-split in larger balance proofs. -/
theorem component_mem_binaryFamily_cases
    {component : Component FGL}
    (h_mem : component ∈ binaryFamilyOpBusEnsemble.ensemble.allTables) :
    component = binaryFamilyOpBusEnsemble.ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.Main.component
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component = ZiskFv.AirsClean.Binary.component
      ∨ component = ZiskFv.AirsClean.BinaryExtension.component := by
  simp [binaryFamilyOpBusEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables] at h_mem
  rcases h_mem with h_verifier | h_binaryExtension | h_binary | h_binaryAdd | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inr (Or.inr (Or.inr h_binaryExtension)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_binary)))
  · exact Or.inr (Or.inr (Or.inl h_binaryAdd))
  · exact Or.inr (Or.inl h_main)
  · cases h_empty

/-- Project the Binary-family ensemble's `BalancedChannels` hypothesis to
    the concrete operation-bus interaction list. -/
theorem opBus_balanced_of_witness
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith OpBusChannel.toRaw) := by
  have h := h_balanced OpBusChannel.toRaw (by
    change OpBusChannel.toRaw ∈ [OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Clean balance gives the first replacement shape for the old op-bus
    permutation axiom: an active Main-side interaction (`mult = -1`) has a
    same-message counterpart whose multiplicity is neither a pull nor an
    inactive zero row. Later C7 lemmas specialize the counterpart to one of
    the Binary-family provider components using the component
    interaction-shape lemmas. -/
theorem exists_matching_nonzero_nonpull_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith OpBusChannel.toRaw)
    (opBus_balanced_of_witness witness h_balanced)
    mainInteraction h_mem h_active

/-- Compatibility projection for existing C7 callers that only need the
    older non-pull shape. -/
theorem exists_matching_nonpull_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1 := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, _h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_interaction witness h_balanced h_mem h_active
  exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull⟩

/-- Classify the nonzero non-pull counterpart supplied by balance as not
    coming from the Main component, provided Main rows have already been
    locally ruled out as nonzero non-pulls.

This is the next C7 bridge layer. The `h_main_mults` premise is not a new
trust boundary: it is the still-open local Main-shape obligation that should
be discharged from Main's `is_external_op` boolean constraint without
normalizing the whole `Table.Spec` in this file. -/
theorem exists_matching_nonMain_component_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_main_mults :
      ∀ {table : Table FGL}, table ∈ witness.allTables →
        table.component = ZiskFv.AirsClean.Main.component →
        ∀ {interaction : Interaction FGL},
          interaction ∈ table.interactionsWith OpBusChannel.toRaw →
          interaction.mult = -1 ∨ interaction.mult = 0)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith OpBusChannel.toRaw
            ∧ table.component ≠ ZiskFv.AirsClean.Main.component := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_not_main : table.component ≠ ZiskFv.AirsClean.Main.component := by
    intro h_main
    have h_mult := h_main_mults h_table h_main h_mem_table
    rcases h_mult with h_neg | h_zero
    · exact h_nonpull h_neg
    · exact h_nonzero h_zero
  refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table, h_table,
    h_mem_table, h_not_main⟩
  rw [EnsembleWitness.mem_interactionsWith]
  exact ⟨table, h_table, h_mem_table⟩

end ZiskFv.AirsClean.BinaryFamily
