import ZiskFv.Compliance.TraceLevelExport.BootSegmentMemorySeed

/-!
# Non-vacuity witness for `BootSegmentMemorySeed` (issue #185)

The load-only Spike witness (`ZiskFv/ZiskCircuit/MemTimeline/Spike.lean`) exhibits
the load residual over **empty** initial memory.  But a narrow store's
`StoreRmwPreservedBytesAtPrefix` floor is **false** over empty memory — its
preserved high bytes must already be present.  This module supplies the missing
store half: the preserved-byte floor is satisfiable off a NON-empty seed memory
(the bytes carried in from the previous segment / boot), so a concrete
`StoreRmwMemoryCoherenceEvidence` is **non-vacuously** inhabited — this is the
store-side anti-laundering crux (the empty-memory floor is genuinely false).
Together with the Spike load witness this shows both per-op residuals of
`memEvidence_of_bootSeed` are inhabitable from concrete-seed data.

(The concrete-seed evidence uses the uniform-replay cursor
`stateAt X := { state with mem := replay im X }`, so regs / PC / cycleCount are
carried by the load/store's own Sail `state` and only `.mem` evolves; the earlier
`witnessStore_nondegenerate` side-claim about a mutating cursor described a cursor
the evidence no longer uses and was dropped. The "not a frozen whole-state floor"
property is a property of the `LoadMemoryTimelineCoherenceEvidence` *type* — which
constrains only `.mem`, leaving regs/PC free — established under the #76 floor
section of `trust/trusted-base.md`, not something this witness must re-exhibit.) -/

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

/-- **The store residual is non-vacuously inhabited.** A concrete
    `StoreRmwMemoryCoherenceEvidence` for the store, with the preserved bytes
    supplied by the (non-empty) seed memory — the store half the empty-memory
    Spike witness cannot provide.  Built directly from the concrete-seed reduction
    `storeEvidence_of_loadMemReplay` (the store is the first op, so `priorRows = []`
    and the clean mem-replay equation is `rfl`).  The load half is
    `ZiskFv.ZiskCircuit.MemTimeline.Spike.witness_memoryTraceAgreement`; together
    both `MemoryOpEvidenceFor` residuals are inhabitable from concrete-seed data. -/
theorem witnessStore_evidence
    (regs0 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) (firstPreserved : Nat) :
    StoreRmwMemoryCoherenceEvidence
      (witnessStoreInitState regs0 cs0) witnessStoreRow firstPreserved :=
  storeEvidence_of_loadMemReplay (priorRows := []) (laterRows := [])
    (witnessStoreFacts regs0 cs0)
    rfl
    rfl
    (by
      simpa [witnessStoreFacts, witnessSeedMem, replayMemoryAfterBusRows] using
        storeRmwPreservedBytes_nonvacuous witnessStoreRow firstPreserved)

end ZiskFv.Compliance
