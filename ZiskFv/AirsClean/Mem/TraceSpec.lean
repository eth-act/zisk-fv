import ZiskFv.Airs.Mem
import ZiskFv.AirsClean.Mem.Spec
import ZiskFv.ZiskCircuit.MemTrace

/-!
# Mem Global Trace Spec

This module names the split proof obligations needed to turn generated Mem AIR
rows into the byte-addressed replay object consumed by load soundness.

No accepted-trace packing chain lives here. The bridge must prove generated row
constraints, public row order, and replay facts separately.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.ZiskCircuit.MemTrace

/-- Rows are ordered as the chronological Mem trace consumed by replay. -/
def MemoryBusRowsChronological
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  rows.Pairwise (fun earlier later =>
    earlier.timestamp.toNat <= later.timestamp.toNat)

/-! ## Generated Mem full-trace construction surface -/

/-- All named generated Mem constraints hold for the active row range
represented by `rowCount`. -/
def GeneratedMemRows
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop :=
  ∀ row, row < rowCount →
    ZiskFv.Airs.Mem.generated_every_row segment permutation mem row

/-- Row-order facts extracted from accepted Mem sorting, segment-boundary, and
multiplicity constraints before replay soundness is constructed.

The Mem PIL permits read/read dual rows with equal timestamps; since the raw
memory-bus row shape has no lane tag, those two projected read entries may be
identical. The replay API therefore requires chronological list order, not
`rows.Nodup`. -/
structure GeneratedMemRowOrderFacts
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop where
  chronologicalRows : MemoryBusRowsChronological rows

/-- Replay facts that connect the accepted chronological Mem rows to Sail
memory. These are the semantic facts load soundness consumes after row order
and selected-row coverage fix the relevant prefix. -/
structure GeneratedMemReplayFacts
    (initialState : SailState)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type where
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  prefixReadSound :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound initialMemory rows
  initialAgreement : ReplayMemoryAgreement initialState initialMemory

/-- Projection of the current local Mem bridge obligations from generated Mem
row facts. -/
theorem core_every_row_of_generated_mem_rows
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount row : ℕ}
    (generatedRows : GeneratedMemRows mem segment permutation rowCount)
    (h_row : row < rowCount) :
    ZiskFv.Airs.Mem.core_every_row mem row :=
  ZiskFv.Airs.Mem.core_every_row_of_generated_every_row
    (generatedRows row h_row)

/-- Prefix-indexed replay facts imply the recursive row-level replay predicate
used by the event-level replay bridge. -/
theorem memoryBusRowsReadWriteSound_of_generated_replay_facts
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (facts : GeneratedMemReplayFacts initialState rows) :
    MemoryBusRowsReadWriteSound facts.initialMemory rows :=
  memoryBusRowsReadWriteSound_of_prefixReadSound
    facts.initialMemory rows facts.prefixReadSound

/-- Prefix-indexed replay facts imply event-level `TraceReplaySound` for the
read/write projection of the public memory-bus rows. -/
theorem traceReplaySound_of_generated_replay_facts
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (facts : GeneratedMemReplayFacts initialState rows) :
    TraceReplaySound facts.initialMemory
      (memoryBusTraceEventsToMemTrace (memoryBusTraceEventsOfRows rows)) :=
  traceReplaySound_of_memoryBusRowsReadWriteSound facts.initialMemory rows
    (memoryBusRowsReadWriteSound_of_generated_replay_facts facts)

/-- Row-order facts expose the chronological-row predicate without repacking. -/
theorem chronologicalRows_of_generated_order_facts
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (facts : GeneratedMemRowOrderFacts rows) :
    MemoryBusRowsChronological rows :=
  facts.chronologicalRows

end ZiskFv.AirsClean.Mem
