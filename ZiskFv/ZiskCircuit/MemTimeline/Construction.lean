import ZiskFv.ZiskCircuit.MemTimeline.Linkage
import ZiskFv.ZiskCircuit.MemTimeline.Ordering

/-!
# Memory timeline construction

This module packages the memory-timeline constructor used before removing the
global `h_memory_timeline` premise.  The circuit side supplies generated replay
facts and selected-row coverage; the remaining named boundary is that the Sail
state at the load is the state obtained by replaying the accepted chronological
memory prefix.
-/

namespace ZiskFv.ZiskCircuit.MemTimeline

open Goldilocks
open Air.Flat
open Interaction
open ZiskFv.ZiskCircuit.MemTrace

/-- P4-bound trace/state alignment for a selected accepted memory prefix.

This is intentionally stronger and more structural than the byte-local
`stateBytesAtPrefix` field: P4's accepted-trace construction should identify
the load's Sail state with the result of applying the accepted chronological
memory-bus prefix to the initial Sail state. -/
@[reducible]
def MemoryPrefixStateAlignment
    (initialState state : SailState)
    (priorRows : List (MemoryBusEntry FGL)) : Prop :=
  state = stateAfterMemoryBusRows initialState priorRows

/-- The P4-bound prefix alignment plus generated replay initial agreement gives
the byte-local `stateBytesAtPrefix` field required by
`MemoryTimelineEvidence`. -/
theorem stateBytesAtPrefix_of_memoryPrefixStateAlignment
    {initialState state : SailState}
    {rows priorRows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (h_alignment : MemoryPrefixStateAlignment initialState state priorRows) :
    ReplayMemoryAgreementOnBytes state
      (replayMemoryAfterBusRows facts.initialMemory priorRows)
      entry.ptr.toNat := by
  unfold MemoryPrefixStateAlignment at h_alignment
  subst state
  intro i _hi
  exact
    replayAgreement_after_memoryBusRows
      initialState priorRows facts.initialMemory facts.initialAgreement
      (entry.ptr.toNat + i)

/-- Construct timeline evidence from generated replay facts, a selected trace
split, the selected-read fact, and the named prefix state alignment. -/
@[reducible]
def memoryTimelineEvidence_of_generated_replay_facts
    {initialState state : SailState}
    {rows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (priorRows laterRows : List (MemoryBusEntry FGL))
    (h_traceSplit : rows = priorRows ++ entry :: laterRows)
    (h_selectedRead :
      memoryBusTraceEventOfRow entry = some (MemoryBusTraceEvent.read entry))
    (h_alignment : MemoryPrefixStateAlignment initialState state priorRows) :
    MemoryTimelineEvidence state entry where
  acceptedReplay := acceptedMemoryReplayEvidenceOfGeneratedReplayFacts facts
  priorRows := priorRows
  laterRows := laterRows
  traceSplit := by
    simpa [acceptedMemoryReplayEvidenceOfGeneratedReplayFacts] using h_traceSplit
  selectedRead := h_selectedRead
  stateBytesAtPrefix :=
    stateBytesAtPrefix_of_memoryPrefixStateAlignment
      (entry := entry) facts h_alignment

/-- Load structural promises provide the selected-read tag fact; generated replay
facts and the named prefix alignment provide the rest of the timeline evidence. -/
@[reducible]
def memoryTimelineEvidence_of_load_structural_promises
    {initialState state : SailState}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (ExecutionBusEntry FGL)}
    {e0 e1 e2 : MemoryBusEntry FGL}
    {rows : List (MemoryBusEntry FGL)}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2)
    (priorRows laterRows : List (MemoryBusEntry FGL))
    (h_traceSplit : rows = priorRows ++ e1 :: laterRows)
    (h_alignment : MemoryPrefixStateAlignment initialState state priorRows) :
    MemoryTimelineEvidence state e1 :=
  memoryTimelineEvidence_of_generated_replay_facts
    facts priorRows laterRows h_traceSplit
    (selectedRead_of_load_structural_promises promises)
    h_alignment

/-- Existential selected-row coverage plus a split-indexed prefix alignment gives
nonempty timeline evidence for the load read row. -/
theorem nonempty_memoryTimelineEvidence_of_load_structural_promises_split
    {initialState state : SailState}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (ExecutionBusEntry FGL)}
    {e0 e1 e2 : MemoryBusEntry FGL}
    {rows : List (MemoryBusEntry FGL)}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2)
    (h_split : ∃ priorRows laterRows, rows = priorRows ++ e1 :: laterRows)
    (h_alignment :
      ∀ priorRows laterRows,
        rows = priorRows ++ e1 :: laterRows →
          MemoryPrefixStateAlignment initialState state priorRows) :
    Nonempty (MemoryTimelineEvidence state e1) := by
  obtain ⟨priorRows, laterRows, h_traceSplit⟩ := h_split
  exact
    ⟨memoryTimelineEvidence_of_load_structural_promises
      facts promises priorRows laterRows h_traceSplit
      (h_alignment priorRows laterRows h_traceSplit)⟩

/-- Primary Mem provider coverage, selected-read load tags, and the P4-bound
prefix alignment construct nonempty timeline evidence. -/
theorem nonempty_memoryTimelineEvidence_of_primary_mem_provider_read_match
    {initialState state : SailState}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (ExecutionBusEntry FGL)}
    {e0 e1 e2 : MemoryBusEntry FGL}
    {rows : List (MemoryBusEntry FGL)}
    {table : Table FGL}
    {providerRow : Array FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2)
    (h_embedded : ZiskFv.AirsClean.FullEnsemble.MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e1
        (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
    (h_alignment :
      ∀ priorRows laterRows,
        rows = priorRows ++ e1 :: laterRows →
          MemoryPrefixStateAlignment initialState state priorRows) :
    Nonempty (MemoryTimelineEvidence state e1) :=
  nonempty_memoryTimelineEvidence_of_load_structural_promises_split
    facts promises
    (memoryBusTraceSplit_of_primary_mem_provider_read_match
      h_embedded h_row h_wr h_match)
    h_alignment

/-- Dual Mem provider coverage, selected-read load tags, and the P4-bound prefix
alignment construct nonempty timeline evidence. -/
theorem nonempty_memoryTimelineEvidence_of_dual_mem_provider_read_match
    {initialState state : SailState}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (ExecutionBusEntry FGL)}
    {e0 e1 e2 : MemoryBusEntry FGL}
    {rows : List (MemoryBusEntry FGL)}
    {table : Table FGL}
    {providerRow : Array FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2)
    (h_embedded : ZiskFv.AirsClean.FullEnsemble.MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e1
        (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
    (h_alignment :
      ∀ priorRows laterRows,
        rows = priorRows ++ e1 :: laterRows →
          MemoryPrefixStateAlignment initialState state priorRows) :
    Nonempty (MemoryTimelineEvidence state e1) :=
  nonempty_memoryTimelineEvidence_of_load_structural_promises_split
    facts promises
    (memoryBusTraceSplit_of_dual_mem_provider_read_match
      h_embedded h_row h_match)
    h_alignment

#print axioms stateBytesAtPrefix_of_memoryPrefixStateAlignment
#print axioms memoryTimelineEvidence_of_generated_replay_facts
#print axioms memoryTimelineEvidence_of_load_structural_promises
#print axioms nonempty_memoryTimelineEvidence_of_primary_mem_provider_read_match
#print axioms nonempty_memoryTimelineEvidence_of_dual_mem_provider_read_match

end ZiskFv.ZiskCircuit.MemTimeline
