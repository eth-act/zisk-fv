import ZiskFv.Airs.Mem
import ZiskFv.Airs.Main.Main
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

/-! ## Generated Mem full-trace construction surface

The source `Airs.Mem.generated_every_row` predicate names every generated
Mem row constraint. The semantic replay object above intentionally does not
pretend those algebraic row facts alone prove chronological memory replay:
the accepted full-trace bridge still has to extract row chronology, selected
public rows, prefix read soundness, and initial Sail/replay agreement from the
accepted AIR/Main/Mem trace. `GeneratedMemFullTraceConstruction` is the
non-hidden target for that bridge.
-/

/-- All generated Mem constraints hold for the active row range represented
    by `rowCount`. -/
def GeneratedMemRows
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop :=
  ∀ row, row < rowCount →
    ZiskFv.Airs.Mem.generated_every_row segment permutation mem row

/-- Accepted full Mem trace construction data rooted at the generated Mem
    constraint surface.

The first fields are the actual generated AIR row facts. The remaining fields
are the semantic consequences still needed by load replay. Keeping them in the
same object makes the remaining bridge theorem precise: it must fill these
semantic fields from accepted AIR/Main/Mem full-trace data, not from a load
wrapper or arbitrary Sail memory bytes. -/
structure GeneratedMemFullTraceConstruction
    (initialState : SailState)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type where
  mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  rowCount : ℕ
  generatedRows : GeneratedMemRows mem segment permutation rowCount
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  chronologicalRows : MemoryBusRowsChronological rows
  rowsReadWriteSound :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory rows
  initialAgreement : ReplayMemoryAgreement initialState initialMemory

/-- Generated full-trace construction data lowers to the global Mem row-trace
    object consumed by load replay. -/
def GeneratedMemFullTraceConstruction.toAcceptedFullMemoryBusRowsTrace
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction : GeneratedMemFullTraceConstruction initialState rows) :
    AcceptedFullMemoryBusRowsTrace initialState rows :=
  AcceptedFullMemoryBusRowsTrace.ofReadWriteSound
    construction.initialMemory
    construction.chronologicalRows
    construction.rowsReadWriteSound
    construction.initialAgreement

/-- Projection of the local Mem bridge obligations from generated full-trace
    construction data. -/
theorem core_every_row_of_generated_full_trace
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction : GeneratedMemFullTraceConstruction initialState rows)
    {row : ℕ}
    (h_row : row < construction.rowCount) :
    ZiskFv.Airs.Mem.core_every_row construction.mem row :=
  ZiskFv.Airs.Mem.core_every_row_of_generated_every_row
    (construction.generatedRows row h_row)

/-! ## Accepted AIR/Main/Mem full-trace construction surface -/

/-- Accepted full-trace construction data for the Main/Mem trace slice.

This is the source-facing interface that must eventually be constructed from
the accepted full execution trace. It is parameterized by the concrete Main
AIR trace so the final bridge cannot be stated independently of the program
trace whose load row is being proved. The fields are still the semantic Mem
facts needed by replay: generated Mem row constraints, chronological public
memory-bus rows, read/write replay soundness, and initial Sail/replay memory
agreement. -/
structure AcceptedAirMainMemFullTraceConstruction
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (initialState : SailState)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type where
  mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  rowCount : ℕ
  generatedRows : GeneratedMemRows mem segment permutation rowCount
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  chronologicalRows : MemoryBusRowsChronological rows
  rowsReadWriteSound :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory rows
  initialAgreement : ReplayMemoryAgreement initialState initialMemory

/-- Forget the Main-trace provenance marker and produce the generated Mem
    construction object consumed by the current replay bridge. -/
def AcceptedAirMainMemFullTraceConstruction.toGeneratedMemFullTraceConstruction
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction :
      AcceptedAirMainMemFullTraceConstruction main initialState rows) :
    GeneratedMemFullTraceConstruction initialState rows :=
  { mem := construction.mem
    segment := construction.segment
    permutation := construction.permutation
    rowCount := construction.rowCount
    generatedRows := construction.generatedRows
    initialMemory := construction.initialMemory
    chronologicalRows := construction.chronologicalRows
    rowsReadWriteSound := construction.rowsReadWriteSound
    initialAgreement := construction.initialAgreement }

/-- Program-level accepted AIR/Main/Mem trace data, before selecting the load
    row relevant to one `OpEnvelope`.

This separates the shared trace construction from the per-envelope cursor:
future full-execution integration should construct this object once for the
accepted program trace, then prove selected-prefix coverage for each load
envelope. -/
structure AcceptedAirMainMemFullTrace
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) : Type where
  initialState : SailState
  rows : List (Interaction.MemoryBusEntry FGL)
  construction :
    AcceptedAirMainMemFullTraceConstruction main initialState rows

end ZiskFv.AirsClean.Mem
