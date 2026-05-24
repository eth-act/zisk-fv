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

end ZiskFv.AirsClean.BinaryFamily
