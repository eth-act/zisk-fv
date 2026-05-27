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
      ∨ component = ZiskFv.AirsClean.Mem.componentWithMemBus
      ∨ component =
        ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program := by
  simp [memBusEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
    at h_mem
  rcases h_mem with h_verifier | h_mem | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inl h_mem)
  · exact Or.inr (Or.inr h_main)
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

end ZiskFv.AirsClean.MemFamily
