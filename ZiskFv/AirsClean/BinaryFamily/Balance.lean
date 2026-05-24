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

end ZiskFv.AirsClean.BinaryFamily
