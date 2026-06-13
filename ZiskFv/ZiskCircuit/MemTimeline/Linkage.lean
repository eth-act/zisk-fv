import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.EquivCore.Promises.Load

/-!
# Memory timeline linkage

This module packages the additive linkage pieces used before constructing the
full `MemoryTimelineEvidence`: generated Mem replay facts give accepted replay
evidence, selected rows can be split out of the chronological trace, and load
tags identify the selected row as a memory read.
-/

namespace ZiskFv.ZiskCircuit.MemTimeline

open Goldilocks
open Air.Flat
open Interaction
open ZiskFv.ZiskCircuit.MemTrace

/-- Generated Mem replay facts already contain the three fields required by
`AcceptedMemoryReplayEvidence`. -/
@[reducible]
def acceptedMemoryReplayEvidenceOfGeneratedReplayFacts
    {initialState : SailState}
    {rows : List (MemoryBusEntry FGL)}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows) :
    AcceptedMemoryReplayEvidence :=
  { rows := rows
    initialMemory := facts.initialMemory
    prefixReadSound := facts.prefixReadSound }

/-- A fieldwise operation-bus match is record equality. -/
theorem eq_of_operation_bus_matches_entry
    {F : Type} [Field F]
    {a b : ZiskFv.Airs.OperationBus.OperationBusEntry F}
    (h : ZiskFv.Airs.OperationBus.matches_entry a b) :
    a = b := by
  cases a
  cases b
  simpa [ZiskFv.Airs.OperationBus.matches_entry] using h

/-- A fieldwise memory-bus match is record equality. -/
theorem eq_of_matches_memory_entry
    {a b : MemoryBusEntry FGL}
    (h : ZiskFv.Airs.MemoryBus.matches_memory_entry a b) :
    a = b := by
  cases a
  cases b
  simpa [ZiskFv.Airs.MemoryBus.matches_memory_entry] using h

/-- A selected member of a list can be exposed as a prefix, the member, and a
suffix. -/
theorem exists_split_of_mem {α : Type} {x : α} :
    ∀ {xs : List α}, x ∈ xs → ∃ prior later, xs = prior ++ x :: later
  | [], h => by simp at h
  | y :: ys, h => by
      rcases List.mem_cons.mp h with hxy | hy
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨prior, later, h_split⟩ := exists_split_of_mem (x := x) hy
        exact ⟨y :: prior, later, by simp [h_split]⟩

/-- Trace split data for a selected memory-bus row. -/
structure LocatedMemoryBusEntry
    (rows : List (MemoryBusEntry FGL))
    (entry : MemoryBusEntry FGL) : Type where
  priorRows : List (MemoryBusEntry FGL)
  laterRows : List (MemoryBusEntry FGL)
  traceSplit : rows = priorRows ++ entry :: laterRows

/-- Membership in the chronological row trace gives nonempty split data. -/
theorem locatedMemoryBusEntry_nonempty_of_mem
    {rows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (h_mem : entry ∈ rows) :
    Nonempty (LocatedMemoryBusEntry rows entry) := by
  obtain ⟨priorRows, laterRows, h_split⟩ := exists_split_of_mem h_mem
  exact ⟨{ priorRows := priorRows, laterRows := laterRows, traceSplit := h_split }⟩

/-- Membership in the chronological row trace gives the split shape required by
`MemoryTimelineEvidence.traceSplit`. -/
theorem memoryBusTraceSplit_of_mem
    {rows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (h_mem : entry ∈ rows) :
    ∃ priorRows laterRows, rows = priorRows ++ entry :: laterRows :=
  exists_split_of_mem h_mem

/-- If a selected accepted row matches a provider row already in the
chronological trace, the selected row has the required trace split. -/
theorem memoryBusTraceSplit_of_matched_row_mem
    {rows : List (MemoryBusEntry FGL)}
    {entry provider : MemoryBusEntry FGL}
    (h_provider : provider ∈ rows)
    (h_match : ZiskFv.Airs.MemoryBus.matches_memory_entry entry provider) :
    ∃ priorRows laterRows, rows = priorRows ++ entry :: laterRows := by
  have h_eq : entry = provider := eq_of_matches_memory_entry h_match
  rw [← h_eq] at h_provider
  exact memoryBusTraceSplit_of_mem h_provider

/-- Selected primary Mem provider read coverage, exposed directly as the trace
split needed by the residual memory-timeline evidence. -/
theorem memoryBusTraceSplit_of_primary_mem_provider_read_match
    {table : Table FGL}
    {rows : List (MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : MemoryBusEntry FGL}
    (h_embedded : ZiskFv.AirsClean.FullEnsemble.MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    ∃ priorRows laterRows, rows = priorRows ++ entry :: laterRows :=
  memoryBusTraceSplit_of_mem
    (ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
      h_embedded h_row h_wr h_match)

/-- Selected dual Mem provider read coverage, exposed directly as the trace
split needed by the residual memory-timeline evidence. -/
theorem memoryBusTraceSplit_of_dual_mem_provider_read_match
    {table : Table FGL}
    {rows : List (MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : MemoryBusEntry FGL}
    (h_embedded : ZiskFv.AirsClean.FullEnsemble.MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    ∃ priorRows laterRows, rows = priorRows ++ entry :: laterRows :=
  memoryBusTraceSplit_of_mem
    (ZiskFv.AirsClean.FullEnsemble.mem_dual_read_replay_entry_mem_of_replay_embedded_trace_row_match
      h_embedded h_row h_match)

/-- Load read tags identify the selected memory-bus row as a replay read. -/
theorem selectedRead_of_as_val_eq_two_of_multiplicity_neg_one
    {entry : MemoryBusEntry FGL}
    (h_as : entry.as.val = 2)
    (h_mult : entry.multiplicity = (-1 : FGL)) :
    memoryBusTraceEventOfRow entry = some (MemoryBusTraceEvent.read entry) := by
  have h_as_eq : entry.as = (2 : FGL) := by
    apply Fin.ext
    rw [h_as]
    norm_num
  simp [memoryBusTraceEventOfRow, h_as_eq, h_mult]

/-- Structural load promises expose the selected-read fact for `e1`. -/
theorem selectedRead_of_load_structural_promises
    {state : SailState}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (ExecutionBusEntry FGL)}
    {e0 e1 e2 : MemoryBusEntry FGL}
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2) :
    memoryBusTraceEventOfRow e1 = some (MemoryBusTraceEvent.read e1) :=
  selectedRead_of_as_val_eq_two_of_multiplicity_neg_one
    promises.m1_as promises.m1_mult

#print axioms acceptedMemoryReplayEvidenceOfGeneratedReplayFacts
#print axioms eq_of_operation_bus_matches_entry
#print axioms eq_of_matches_memory_entry
#print axioms memoryBusTraceSplit_of_primary_mem_provider_read_match
#print axioms memoryBusTraceSplit_of_dual_mem_provider_read_match
#print axioms selectedRead_of_load_structural_promises

end ZiskFv.ZiskCircuit.MemTimeline
