import ZiskFv.AirsClean.FullEnsemble

/-!
# Full Clean ensemble balance projections

T7 needs canonical proofs to consume the full Clean ensemble directly,
rather than family-local ensembles.  This module exposes the first reusable
structural facts from `FullEnsemble.fullRv64imEnsemble`: the concrete table
classification and the balanced operation/memory channel projections.

## Trust note

No axioms.  These lemmas only unpack `EnsembleWitness.BalancedChannels` and
the `fullRv64imEnsemble` table list.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- Concrete component classification for the row-coherent full Clean
    ensemble. Components appear newest-first after the empty verifier table,
    matching Clean's `SoundEnsemble.addTable` list discipline. -/
theorem component_mem_fullRv64im_cases
    {length : ℕ} {program : Program length}
    {component : Component FGL}
    (h_mem : component ∈ (fullRv64imEnsemble length program).ensemble.allTables) :
    component = (fullRv64imEnsemble length program).ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.MemAlignReadByte.component
      ∨ component = ZiskFv.AirsClean.MemAlignByte.component
      ∨ component = ZiskFv.AirsClean.MemAlign.component
      ∨ component = ZiskFv.AirsClean.Mem.componentWithMemBus
      ∨ component = ZiskFv.AirsClean.ArithDiv.component
      ∨ component = ZiskFv.AirsClean.ArithMul.component
      ∨ component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.Binary.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
    at h_mem
  rcases h_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_memAlign)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_mem))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithDiv)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithMul))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binExt)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binary))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binaryAdd)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main)))))))))
  · cases h_empty

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute operation-bus interactions. -/
theorem verifierTable_interactionsWith_opBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      OpBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute memory-bus interactions. -/
theorem verifierTable_interactionsWith_memBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      MemBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- Project the full ensemble's `BalancedChannels` hypothesis to the
    concrete operation-bus interaction list. -/
theorem opBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith OpBusChannel.toRaw) := by
  have h := h_balanced OpBusChannel.toRaw (by
    change OpBusChannel.toRaw ∈ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Project the full ensemble's `BalancedChannels` hypothesis to the
    concrete memory-bus interaction list. -/
theorem memBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith MemBusChannel.toRaw) := by
  have h := h_balanced MemBusChannel.toRaw (by
    change MemBusChannel.toRaw ∈ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

end ZiskFv.AirsClean.FullEnsemble
