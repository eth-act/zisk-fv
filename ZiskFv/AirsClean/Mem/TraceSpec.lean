import ZiskFv.AirsClean.Mem.Spec
import ZiskFv.ZiskCircuit.MemTrace

/-!
# Mem Global Trace Spec

This module names the full-trace Mem facts needed to construct the
byte-addressed replay object consumed by load soundness.

The local `Mem.Spec` layer covers only the 9 F-typed per-row constraints.
This global spec is deliberately separate: future extraction work should prove
these fields from the skipped mixed F/ExtF constraints, segment carry facts,
dual-memory emission, and accepted memory-bus row coverage.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.ZiskCircuit.MemTrace

/-- Active memory read row in the public memory-bus row projection. -/
def MemoryBusRowIsRead (row : Interaction.MemoryBusEntry FGL) : Prop :=
  row.as = (2 : FGL) ∧ row.multiplicity = (-1 : FGL)

/-- Active memory write row in the public memory-bus row projection. -/
def MemoryBusRowIsWrite (row : Interaction.MemoryBusEntry FGL) : Prop :=
  row.as = (2 : FGL) ∧ row.multiplicity = (1 : FGL)

/-- Rows are already ordered as the chronological Mem trace consumed by
    replay. This is the public-row version of the Mem sorted-address/step
    obligation; the eventual AIR bridge should derive it from the Mem
    permutation and segment-order constraints. -/
def MemoryBusRowsChronological
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  rows.Pairwise (fun earlier later =>
    earlier.timestamp.toNat <= later.timestamp.toNat)

/-- Adjacent same-address reads preserve the emitted value. This names the
    row-local value carry fact that must be supplied by Mem continuity for
    sorted rows. -/
def MemoryBusRowsSameAddressValuePreservation
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ priorRows previous row laterRows,
    rows = priorRows ++ previous :: row :: laterRows →
      MemoryBusRowIsRead previous →
        MemoryBusRowIsRead row →
          previous.ptr = row.ptr →
            previous.value_0 = row.value_0 ∧ previous.value_1 = row.value_1

/-- Writes update the replay memory in the same public-row shape consumed by
    the load bridge. The proof is expected to come from accepted Mem write
    rows and their memory-bus emission. -/
def MemoryBusRowsWriteUpdateSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ priorRows row laterRows,
    rows = priorRows ++ row :: laterRows →
      MemoryBusRowIsWrite row →
        replayMemoryAfterBusRows initialMemory (priorRows ++ [row]) =
          replayStoreEvent
            (replayMemoryAfterBusRows initialMemory priorRows)
            (storeEventOfEntry row)

/-- The public raw-row replay function updates active memory writes exactly
    as `storeEventOfEntry` records them. This is definitional for the replay
    model, so callers of the global Mem trace object should not have to supply
    it as a separate burden. -/
theorem memoryBusRowsWriteUpdateSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (Interaction.MemoryBusEntry FGL)) :
    MemoryBusRowsWriteUpdateSound initialMemory rows := by
  intro priorRows row _laterRows _h_split h_write
  obtain ⟨h_as, h_mult⟩ := h_write
  simp [replayMemoryAfterBusRows, replayMemoryAfterBusRow, h_as, h_mult]

/-- Active same-address rows are timestamp-monotone. This is separated from
    `MemoryBusRowsChronological` because the extracted AIR proof will likely
    discharge it through address/step sortedness constraints. -/
def MemoryBusRowsEventOrderingSound
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ priorRows earlier middleRows later laterRows,
    rows = priorRows ++ earlier :: middleRows ++ later :: laterRows →
      (MemoryBusRowIsRead earlier ∨ MemoryBusRowIsWrite earlier) →
        (MemoryBusRowIsRead later ∨ MemoryBusRowIsWrite later) →
          earlier.ptr = later.ptr →
            earlier.timestamp.toNat <= later.timestamp.toNat

/-- Chronological raw rows imply the selected same-address event-ordering
    consequence. Address equality and active tags are retained in the
    predicate for future AIR-side extraction, but the public-row statement is
    just a projection of `Pairwise` chronology. -/
theorem memoryBusRowsEventOrderingSound_of_chronological
    (rows : List (Interaction.MemoryBusEntry FGL))
    (h_chronological : MemoryBusRowsChronological rows) :
    MemoryBusRowsEventOrderingSound rows := by
  intro priorRows earlier middleRows later laterRows h_split _h_earlier
    _h_later _h_ptr
  rw [h_split] at h_chronological
  rw [MemoryBusRowsChronological] at h_chronological
  rw [List.pairwise_iff_forall_sublist] at h_chronological
  exact h_chronological (by simp)

/-- Segment-boundary carry facts for chronological rows. The public row type
    does not expose the Mem segment accumulator columns, so this predicate
    records the row-observable consequence needed by replay: each selected
    prefix remains a chronological prefix of the full row list. -/
def MemoryBusRowsSegmentCarrySound
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ priorRows row laterRows,
    rows = priorRows ++ row :: laterRows →
      priorRows.Pairwise (fun earlier later =>
        earlier.timestamp.toNat <= later.timestamp.toNat)

/-- Every selected prefix of chronological raw rows is chronological. The AIR
    segment-carry proof still has to justify that the public rows are the
    accepted chronological rows; once that list is fixed, this prefix property
    is a standard `Pairwise` projection. -/
theorem memoryBusRowsSegmentCarrySound_of_chronological
    (rows : List (Interaction.MemoryBusEntry FGL))
    (h_chronological : MemoryBusRowsChronological rows) :
    MemoryBusRowsSegmentCarrySound rows := by
  intro priorRows row laterRows h_split
  rw [h_split] at h_chronological
  rw [MemoryBusRowsChronological] at h_chronological
  exact (List.pairwise_append.1 h_chronological).1

/-- Dual-memory emission coverage at the public row layer: every active memory
    row must project to a replay event. The stronger AIR-side proof should
    additionally show that primary and dual Mem lanes emit the expected rows
    before this predicate is constructed. -/
def MemoryBusRowsDualEventsSound
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ row,
    row ∈ rows →
      (MemoryBusRowIsRead row ∨ MemoryBusRowIsWrite row) →
        ∃ event, memoryBusTraceEventOfRow row = some event

/-- Active read/write memory rows always project to a concrete replay event.
    The AIR-side dual-emission work still has to expose both primary and dual
    MemBus rows, but once a row is in the public chronological row list this
    projection is pure. -/
theorem memoryBusRowsDualEventsSound
    (rows : List (Interaction.MemoryBusEntry FGL)) :
    MemoryBusRowsDualEventsSound rows := by
  intro row _h_mem h_active
  rcases h_active with h_read | h_write
  · obtain ⟨h_as, h_mult⟩ := h_read
    exact ⟨ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read row,
      by simp [memoryBusTraceEventOfRow, h_as, h_mult]⟩
  · obtain ⟨h_as, h_mult⟩ := h_write
    have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
      native_decide
    exact ⟨ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.write row,
      by simp [memoryBusTraceEventOfRow, h_as, h_mult, h_one_ne_neg_one]⟩

/-- Accepted full Mem trace facts for chronological raw memory-bus rows.

The rows are already projected to the public memory-bus row type used by the
load replay layer. `prefixReadSound` is the semantic content needed for loads:
every active memory read row emits the value obtained by replaying the
chronological prefix before that row. The remaining fields name the global AIR
obligations that are actually consumed by the replay bridge and must
eventually be proved from accepted Mem trace data rather than from caller
evidence. -/
structure AcceptedFullMemoryBusRowsTrace
    (initialState : SailState)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type where
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  chronologicalRows : MemoryBusRowsChronological rows
  prefixReadSound : MemoryBusRowsPrefixReadSound initialMemory rows
  initialAgreement : ReplayMemoryAgreement initialState initialMemory

/-- Build the accepted global Mem row trace from a sequential row replay
    proof. This is useful for the eventual AIR bridge, where Mem continuity is
    naturally proved by walking the chronological row list. -/
def AcceptedFullMemoryBusRowsTrace.ofReadWriteSound
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_chronological : MemoryBusRowsChronological rows)
    (h_rows : MemoryBusRowsReadWriteSound initialMemory rows)
    (h_initial : ReplayMemoryAgreement initialState initialMemory) :
    AcceptedFullMemoryBusRowsTrace initialState rows :=
  { initialMemory := initialMemory
    chronologicalRows := h_chronological
    prefixReadSound :=
      memoryBusRowsPrefixReadSound_of_readWriteSound
        initialMemory rows h_rows
    initialAgreement := h_initial }

/-- Lower the global Mem trace spec to the replay construction object consumed
    by the existing memory-load bridge. -/
def AcceptedFullMemoryBusRowsTrace.toRowsTraceConstruction
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (trace : AcceptedFullMemoryBusRowsTrace initialState rows) :
    AcceptedMemoryBusRowsTraceConstruction initialState rows :=
  { initialMemory := trace.initialMemory
    storeReplaySound := MemoryBusRowsWriteUpdateSound trace.initialMemory rows
    eventOrderingSound := MemoryBusRowsEventOrderingSound rows
    segmentCarrySound := MemoryBusRowsSegmentCarrySound rows
    dualEventsSound := MemoryBusRowsDualEventsSound rows
    rowsReadWriteSound :=
      memoryBusRowsReadWriteSound_of_prefixReadSound
        trace.initialMemory rows trace.prefixReadSound
    initialAgreement := trace.initialAgreement }

end ZiskFv.AirsClean.Mem
