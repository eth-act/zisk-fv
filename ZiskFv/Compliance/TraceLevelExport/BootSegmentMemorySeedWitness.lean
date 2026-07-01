import ZiskFv.Compliance.TraceLevelExport.BootSegmentMemorySeed

/-!
# Non-vacuity witness for `BootSegmentMemorySeed` (issue #185)

The load-only Spike witness (`ZiskFv/ZiskCircuit/MemTimeline/Spike.lean`) exhibits
the shared-seed data (`GeneratedMemReplayFacts`, `RowTraceCoherence`) and the load
residual over **empty** initial memory.  But a narrow store's
`StoreRmwPreservedBytesAtPrefix` floor is **false** over empty memory — its
preserved high bytes must already be present.  This module supplies the missing
store half: the preserved-byte floor is satisfiable off a NON-empty seed memory
(the bytes carried in from the previous segment / boot), and hence a concrete
`StoreRmwMemoryCoherenceEvidence` is non-vacuously inhabited — with the store's
Sail state genuinely differing from the initial state in `regs` and `cycleCount`,
so this is not the frozen-state laundering floor.  Together with the Spike load
witness this shows both per-op residuals of `memEvidence_of_bootSeed` are
inhabitable from shared-seed-shaped data. -/

namespace ZiskFv.Compliance

open Interaction
open ZiskFv.ZiskCircuit.MemTrace

/-- **The store-side non-vacuity crux.** After a full eight-lane write of `entry`,
    the replay memory contains exactly `entry`'s committed bytes, so *every*
    preserved high byte is present — `StoreRmwPreservedBytesAtPrefix` holds for any
    `firstPreserved`.  Over empty memory this is false, which is why the load-only
    Spike witness does not cover the store side. -/
theorem storeRmwPreservedBytes_nonvacuous
    (entry : MemoryBusEntry FGL) (firstPreserved : Nat) :
    StoreRmwPreservedBytesAtPrefix
      (writeMemoryOfEntry ({} : Std.ExtHashMap Nat (BitVec 8)) entry) entry firstPreserved := by
  have h := readEventReplayAgreement_of_writeMemoryOfEntry_same
    (mem := ({} : Std.ExtHashMap Nat (BitVec 8)))
    (writeEntry := entry) (readEntry := entry) rfl rfl rfl
  simp only [ReadEventReplayAgreement, eventOfEntry_byteAt] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  intro i _hfp hi8
  interval_cases i
  · simpa using h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-! ## A concrete `StoreRmwMemoryCoherenceEvidence` inhabitant

The store is the first op; its preserved high bytes are supplied by the seed
memory `writeMemoryOfEntry {} witnessStoreRow` (the boot / cross-segment carry-in).
The cursor state after the store differs from the initial state in `regs` and
`cycleCount`, so this is not the frozen-state floor. -/

open ZiskFv.ZiskCircuit.MemTimeline.Spike (witnessStoreRow)

/-- Seed memory carrying the store's committed bytes. -/
noncomputable def witnessSeedMem : Std.ExtHashMap Nat (BitVec 8) :=
  writeMemoryOfEntry ({} : Std.ExtHashMap Nat (BitVec 8)) witnessStoreRow

/-- Segment-entry Sail state: memory already carries the store's preserved bytes. -/
noncomputable def witnessStoreInitState
    (regs0 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) : SailState :=
  { regs := regs0, choiceState := cs0, mem := witnessSeedMem, tags := (),
    cycleCount := 0, sailOutput := #[] }

/-- Cursor-indexed state: after the store, `regs` and `cycleCount` are mutated. -/
noncomputable def witnessStoreStateAt
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    List (MemoryBusEntry FGL) → SailState
  | [] => witnessStoreInitState regs0 cs0
  | _ =>
      { regs := regs1, choiceState := cs0,
        mem := writeMemoryOfEntry witnessSeedMem witnessStoreRow,
        tags := (), cycleCount := 99, sailOutput := #[] }

/-- `prefixReadSound` for `[witnessStoreRow]` is vacuous: the only row is a write
    (`multiplicity = 1 ≠ -1`), so there is no read to constrain. -/
theorem witnessStore_prefixReadSound :
    MemoryBusRowsPrefixReadSound witnessSeedMem [witnessStoreRow] := by
  intro priorRows row laterRows h_split _h_as h_mult
  rcases priorRows with _ | ⟨a, rest⟩
  · simp only [List.nil_append, List.cons.injEq] at h_split
    rw [← h_split.1] at h_mult
    simp only [witnessStoreRow] at h_mult
    exact absurd h_mult (by decide)
  · simp only [List.cons_append, List.cons.injEq] at h_split
    exact absurd h_split.2 (by simp)

/-- Replay facts for the single-store witness segment. -/
noncomputable def witnessStoreFacts
    (regs0 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts
      (witnessStoreInitState regs0 cs0) [witnessStoreRow] :=
  { initialMemory := witnessSeedMem
    prefixReadSound := witnessStore_prefixReadSound
    initialAgreement := fun _ => rfl }

/-- Whole-sequence coherence over `[witnessStoreRow]`: the single write step is
    discharged from the canonical write-entry transition. -/
theorem witnessStore_rowTraceCoherence
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    ZiskFv.ZiskCircuit.MemTimeline.Spike.RowTraceCoherence
      (witnessStoreStateAt regs0 regs1 cs0) [] [witnessStoreRow] := by
  refine ⟨?_, trivial⟩
  intro mem h_agree
  exact ZiskFv.ZiskCircuit.MemTimeline.Spike.rowStep_store_entry
    (witnessStoreStateAt regs0 regs1 cs0 [])
    (witnessStoreStateAt regs0 regs1 cs0 ([] ++ [witnessStoreRow]))
    witnessStoreRow (by simp [witnessStoreRow]) (by simp [witnessStoreRow])
    rfl mem h_agree

/-- **The store residual is non-vacuously inhabited.** A concrete
    `StoreRmwMemoryCoherenceEvidence` for the store, with the preserved bytes
    supplied by the (non-empty) seed memory — the store half the empty-memory
    Spike witness cannot provide.  The load half is
    `ZiskFv.ZiskCircuit.MemTimeline.Spike.witness_memoryTraceAgreement`; together
    both `MemoryOpEvidenceFor` residuals are inhabitable from seed-shaped data. -/
theorem witnessStore_evidence
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) (firstPreserved : Nat) :
    StoreRmwMemoryCoherenceEvidence
      (witnessStoreInitState regs0 cs0) witnessStoreRow firstPreserved :=
  storeCoherence_of_shared (priorRows := []) (laterRows := [])
    (witnessStoreFacts regs0 cs0)
    (witnessStoreStateAt regs0 regs1 cs0)
    rfl
    (witnessStore_rowTraceCoherence regs0 regs1 cs0)
    rfl
    rfl
    (by
      simpa [witnessStoreFacts, witnessSeedMem, replayMemoryAfterBusRows] using
        storeRmwPreservedBytes_nonvacuous witnessStoreRow firstPreserved)

/-- **Non-degeneracy.** With `regs1 ≠ regs0`, the post-store cursor state's `regs`
    and `cycleCount` both differ from the segment initial state's — the non-frozen
    case the whole-state alignment cannot express. -/
theorem witnessStore_nondegenerate
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) (h_regs : regs1 ≠ regs0) :
    (witnessStoreStateAt regs0 regs1 cs0 [witnessStoreRow]).regs
        ≠ (witnessStoreStateAt regs0 regs1 cs0 []).regs
    ∧ (witnessStoreStateAt regs0 regs1 cs0 [witnessStoreRow]).cycleCount
        ≠ (witnessStoreStateAt regs0 regs1 cs0 []).cycleCount := by
  refine ⟨?_, ?_⟩
  · simpa [witnessStoreStateAt, witnessStoreInitState] using h_regs
  · simp [witnessStoreStateAt, witnessStoreInitState]

end ZiskFv.Compliance
