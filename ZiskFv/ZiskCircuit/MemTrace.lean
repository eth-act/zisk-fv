import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.SailSpec.Auxiliaries

/-!
# Mem trace vocabulary

This module contains the theorem-shaped replacement vocabulary for the
load-side Sail memory bridge.  The local load theorem in `MemModel` will
consume explicit agreement between a selected memory event and the Sail byte
map; whole-trace soundness stays separate from the opcode wrapper layer.
-/

namespace ZiskFv.ZiskCircuit.MemTrace

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)

abbrev SailState :=
  PreSail.SequentialState RegisterType Sail.trivialChoiceSource

/-- Primary or dual Mem operation selected from the Mem trace. -/
inductive MemLane where
  | primary
  | dual
deriving DecidableEq, Repr

/-- A byte-addressed Mem trace event.  `ptr` is the PIL memory-bus byte
address, not the raw Mem AIR word-address column. -/
structure MemEvent where
  lane : MemLane
  op : FGL
  ptr : FGL
  timestamp : FGL
  width : FGL
  value_0 : FGL
  value_1 : FGL

/-- The eight byte lanes carried by an event. -/
@[reducible]
def MemEvent.byteAt (e : MemEvent) (i : ℕ) : FGL :=
  ZiskFv.Channels.MemoryBusBytes.byteAt
    { as := 2
      ptr := e.ptr
      value_0 := e.value_0
      value_1 := e.value_1
      timestamp := e.timestamp
      multiplicity := 0 } i

/-- Sail-side byte agreement for the selected load event. -/
def MemoryTraceAgreement
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent) : Prop :=
  state.mem[event.ptr.toNat]? = .some (event.byteAt 0)
  ∧ state.mem[event.ptr.toNat + 1]? = .some (event.byteAt 1)
  ∧ state.mem[event.ptr.toNat + 2]? = .some (event.byteAt 2)
  ∧ state.mem[event.ptr.toNat + 3]? = .some (event.byteAt 3)
  ∧ state.mem[event.ptr.toNat + 4]? = .some (event.byteAt 4)
  ∧ state.mem[event.ptr.toNat + 5]? = .some (event.byteAt 5)
  ∧ state.mem[event.ptr.toNat + 6]? = .some (event.byteAt 6)
  ∧ state.mem[event.ptr.toNat + 7]? = .some (event.byteAt 7)

/-- Apply a store byte to a replay memory. The replay model is deliberately
byte-addressed, matching Sail's memory map and the PIL memory-bus pointer. -/
def replayStoreByte
    (mem : Std.ExtHashMap Nat (BitVec 8)) (addr : Nat) (byte : BitVec 8) :
    Std.ExtHashMap Nat (BitVec 8) :=
  mem.insert addr byte

/-- Replay a store event into a byte-addressed memory map. The Mem AIR emits
8 lanes; narrow store callers use the event width to select the written
prefix. -/
def replayStoreEvent (mem : Std.ExtHashMap Nat (BitVec 8)) (event : MemEvent) :
    Std.ExtHashMap Nat (BitVec 8) :=
  let mem := if 0 < event.width.toNat then
    replayStoreByte mem event.ptr.toNat (event.byteAt 0) else mem
  let mem := if 1 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 1) (event.byteAt 1) else mem
  let mem := if 2 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 2) (event.byteAt 2) else mem
  let mem := if 3 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 3) (event.byteAt 3) else mem
  let mem := if 4 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 4) (event.byteAt 4) else mem
  let mem := if 5 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 5) (event.byteAt 5) else mem
  let mem := if 6 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 6) (event.byteAt 6) else mem
  if 7 < event.width.toNat then
    replayStoreByte mem (event.ptr.toNat + 7) (event.byteAt 7) else mem

/-- Replay all store events in order. Loads do not mutate replay memory. -/
def replayEvents (init : Std.ExtHashMap Nat (BitVec 8)) :
    List MemEvent → Std.ExtHashMap Nat (BitVec 8)
  | [] => init
  | event :: rest =>
      let mem :=
        if event.op = (2 : FGL) then replayStoreEvent init event else init
      replayEvents mem rest

/-- Pointwise agreement between Sail memory and the replay memory at a cursor. -/
def ReplayMemoryAgreement
    (state : SailState)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ addr : Nat, state.mem[addr]? = mem[addr]?

/-- A Sail memory transition that matches one Mem trace event for every
    replay memory currently agreeing with the pre-state. Loads leave replay
    memory unchanged; stores update it with `replayStoreEvent`. -/
def EventReplayStep
    (before after : SailState) (event : MemEvent) : Prop :=
  ∀ mem : Std.ExtHashMap Nat (BitVec 8),
    ReplayMemoryAgreement before mem →
      ReplayMemoryAgreement after
        (if event.op = (2 : FGL) then replayStoreEvent mem event else mem)

/-- Per-event replay steps for a prefix, indexed by the already-consumed
    prefix so callers can provide the Sail state at each execution cursor. -/
def PrefixReplayStepsFrom
    (stateAt : List MemEvent → SailState) :
    List MemEvent → List MemEvent → Prop
  | _done, [] => True
  | done, event :: rest =>
      EventReplayStep (stateAt done) (stateAt (done ++ [event])) event
      ∧ PrefixReplayStepsFrom stateAt (done ++ [event]) rest

/-- Prefix replay steps restrict to any shorter prefix. -/
theorem prefixReplayStepsFrom_of_append
    (stateAt : List MemEvent → SailState)
    (done pref suffix : List MemEvent)
    (h_steps : PrefixReplayStepsFrom stateAt done (pref ++ suffix)) :
    PrefixReplayStepsFrom stateAt done pref := by
  induction pref generalizing done with
  | nil =>
      trivial
  | cons event rest ih =>
      simp [PrefixReplayStepsFrom] at h_steps ⊢
      exact ⟨h_steps.1, ih (done ++ [event]) h_steps.2⟩

/-- Replay agreement after executing a prefix, proved by induction from
    initial agreement and per-event memory transition steps. -/
theorem replayAgreement_of_prefixReplayStepsFrom
    (stateAt : List MemEvent → SailState)
    (done events : List MemEvent)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (h_initial : ReplayMemoryAgreement (stateAt done) mem)
    (h_steps : PrefixReplayStepsFrom stateAt done events) :
    ReplayMemoryAgreement (stateAt (done ++ events))
      (replayEvents mem events) := by
  induction events generalizing done mem with
  | nil =>
      simpa [PrefixReplayStepsFrom, replayEvents] using h_initial
  | cons event rest ih =>
      simp [PrefixReplayStepsFrom] at h_steps
      have h_next :
          ReplayMemoryAgreement (stateAt (done ++ [event]))
            (if event.op = (2 : FGL) then replayStoreEvent mem event else mem) :=
        h_steps.1 mem h_initial
      have h_tail :=
        ih (done ++ [event])
          (if event.op = (2 : FGL) then replayStoreEvent mem event else mem)
          h_next h_steps.2
      simpa [replayEvents, List.append_assoc] using h_tail

/-- A read event's emitted byte lanes agree with the replay memory at that
event's byte pointer. -/
def ReadEventReplayAgreement
    (mem : Std.ExtHashMap Nat (BitVec 8)) (event : MemEvent) : Prop :=
  mem[event.ptr.toNat]? = .some (event.byteAt 0)
  ∧ mem[event.ptr.toNat + 1]? = .some (event.byteAt 1)
  ∧ mem[event.ptr.toNat + 2]? = .some (event.byteAt 2)
  ∧ mem[event.ptr.toNat + 3]? = .some (event.byteAt 3)
  ∧ mem[event.ptr.toNat + 4]? = .some (event.byteAt 4)
  ∧ mem[event.ptr.toNat + 5]? = .some (event.byteAt 5)
  ∧ mem[event.ptr.toNat + 6]? = .some (event.byteAt 6)
  ∧ mem[event.ptr.toNat + 7]? = .some (event.byteAt 7)

/-- Combine Sail/replay state agreement at a cursor with read-row replay
soundness for the selected event. -/
theorem memoryTraceAgreement_of_replayAgreement
    (state : SailState)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (event : MemEvent)
    (h_state : ReplayMemoryAgreement state mem)
    (h_read : ReadEventReplayAgreement mem event) :
    MemoryTraceAgreement state event := by
  unfold MemoryTraceAgreement
  unfold ReadEventReplayAgreement at h_read
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state event.ptr.toNat]
    exact h_read.1
  · rw [h_state (event.ptr.toNat + 1)]
    exact h_read.2.1
  · rw [h_state (event.ptr.toNat + 2)]
    exact h_read.2.2.1
  · rw [h_state (event.ptr.toNat + 3)]
    exact h_read.2.2.2.1
  · rw [h_state (event.ptr.toNat + 4)]
    exact h_read.2.2.2.2.1
  · rw [h_state (event.ptr.toNat + 5)]
    exact h_read.2.2.2.2.2.1
  · rw [h_state (event.ptr.toNat + 6)]
    exact h_read.2.2.2.2.2.2.1
  · rw [h_state (event.ptr.toNat + 7)]
    exact h_read.2.2.2.2.2.2.2

/-- Whole-trace replay soundness. At each event, read rows must emit the
bytes currently present in the replay memory; store rows update replay memory
for the remaining suffix. -/
def TraceReplaySound
    (mem : Std.ExtHashMap Nat (BitVec 8)) : List MemEvent → Prop
  | [] => True
  | event :: rest =>
      (event.op = (1 : FGL) → ReadEventReplayAgreement mem event)
      ∧ TraceReplaySound
          (if event.op = (2 : FGL) then replayStoreEvent mem event else mem)
          rest

/-- Project a selected read event's replay agreement out of whole-trace
soundness at the corresponding prefix cursor. -/
theorem readEventReplayAgreement_of_trace_sound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (priorEvents : List MemEvent)
    (event : MemEvent)
    (laterEvents : List MemEvent)
    (h_sound :
      TraceReplaySound initialMemory (priorEvents ++ event :: laterEvents))
    (h_read : event.op = (1 : FGL)) :
    ReadEventReplayAgreement (replayEvents initialMemory priorEvents) event := by
  induction priorEvents generalizing initialMemory with
  | nil =>
      simpa [TraceReplaySound] using h_sound.1 h_read
  | cons priorEvent priorEvents ih =>
      simp only [List.cons_append, replayEvents] at h_sound ⊢
      exact ih
        (if priorEvent.op = (2 : FGL) then
          replayStoreEvent initialMemory priorEvent
        else
          initialMemory)
        h_sound.2

/-- Convert a memory-bus entry into the event shape used by the local load
theorem. -/
@[reducible]
def eventOfEntry (e : MemoryBusEntry FGL) : MemEvent where
  lane := .primary
  op := 1
  ptr := e.ptr
  timestamp := e.timestamp
  width := 8
  value_0 := e.value_0
  value_1 := e.value_1

/-- Convert a memory-bus store entry into the event shape used by replay.
ZisK's memory bus carries eight byte lanes for memory writes. Narrow stores
preserve the untouched lanes in the emitted entry, so the bus-effect memory
update and the replay update are both eight-byte writes at this layer. -/
@[reducible]
def storeEventOfEntry (e : MemoryBusEntry FGL) : MemEvent where
  lane := .primary
  op := 2
  ptr := e.ptr
  timestamp := e.timestamp
  width := 8
  value_0 := e.value_0
  value_1 := e.value_1

/-- The Sail/bus-effect memory update for an eight-lane memory write entry. -/
@[reducible]
def writeMemoryOfEntry
    (mem : Std.ExtHashMap Nat (BitVec 8)) (e : MemoryBusEntry FGL) :
    Std.ExtHashMap Nat (BitVec 8) :=
  (((((((mem.insert e.ptr.toNat (byteAt e 0)
    ).insert (e.ptr.toNat + 1) (byteAt e 1)
    ).insert (e.ptr.toNat + 2) (byteAt e 2)
    ).insert (e.ptr.toNat + 3) (byteAt e 3)
    ).insert (e.ptr.toNat + 4) (byteAt e 4)
    ).insert (e.ptr.toNat + 5) (byteAt e 5)
    ).insert (e.ptr.toNat + 6) (byteAt e 6)
    ).insert (e.ptr.toNat + 7) (byteAt e 7)

/-- The zero-valued memory-bus entry at the same pointer as `e`.
This is used to build the finite replay memory that supplies the initial
zero value for reads before the first write to an address. -/
@[reducible]
def zeroedMemoryEntryOfEntry (e : MemoryBusEntry FGL) :
    MemoryBusEntry FGL :=
  { e with value_0 := 0, value_1 := 0 }

/-- Preload replay memory with eight zero bytes at one memory-bus row's
pointer. -/
@[reducible]
def zeroMemoryOfEntry
    (mem : Std.ExtHashMap Nat (BitVec 8)) (e : MemoryBusEntry FGL) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeMemoryOfEntry mem (zeroedMemoryEntryOfEntry e)

/-- Finite zero-preload memory for the pointers mentioned by a row list. -/
@[reducible]
def zeroMemoryOfRows (rows : List (MemoryBusEntry FGL)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  rows.foldl zeroMemoryOfEntry ({} : Std.ExtHashMap Nat (BitVec 8))

@[simp]
lemma eventOfEntry_byteAt (e : MemoryBusEntry FGL) (i : ℕ) :
    (eventOfEntry e).byteAt i = byteAt e i := by
  unfold eventOfEntry MemEvent.byteAt byteAt
  simp

@[simp]
lemma storeEventOfEntry_byteAt (e : MemoryBusEntry FGL) (i : ℕ) :
    (storeEventOfEntry e).byteAt i = byteAt e i := by
  unfold storeEventOfEntry MemEvent.byteAt byteAt
  simp

@[simp]
lemma replayStoreEvent_storeEventOfEntry
    (mem : Std.ExtHashMap Nat (BitVec 8)) (e : MemoryBusEntry FGL) :
    replayStoreEvent mem (storeEventOfEntry e) = writeMemoryOfEntry mem e := by
  simp [replayStoreEvent, replayStoreByte, storeEventOfEntry, writeMemoryOfEntry]

/-- After replaying an eight-byte write entry, a read entry with the same byte
pointer and value chunks agrees with replay memory byte-for-byte.

This is the row-local write→read step used by the Mem AIR prefix-read proof
after same-address/value carry has identified the current read with the
previous write row. -/
theorem readEventReplayAgreement_of_writeMemoryOfEntry_same
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {writeEntry readEntry : MemoryBusEntry FGL}
    (h_ptr : readEntry.ptr = writeEntry.ptr)
    (h_value_0 : readEntry.value_0 = writeEntry.value_0)
    (h_value_1 : readEntry.value_1 = writeEntry.value_1) :
    ReadEventReplayAgreement (writeMemoryOfEntry mem writeEntry)
      (eventOfEntry readEntry) := by
  cases writeEntry
  cases readEntry
  simp only at h_ptr h_value_0 h_value_1
  subst h_ptr
  subst h_value_0
  subst h_value_1
  simp only [ReadEventReplayAgreement, writeMemoryOfEntry, MemEvent.byteAt,
    ZiskFv.Channels.MemoryBusBytes.byteAt, Std.ExtHashMap.getElem?_insert,
    beq_iff_eq]
  set_option synthInstance.maxHeartbeats 400000 in grind

/-- Two memory-bus entries address disjoint eight-byte ranges. -/
def MemoryBusEntryByteDisjoint
    (left right : MemoryBusEntry FGL) : Prop :=
  ∀ i j, i < 8 → j < 8 → left.ptr.toNat + i ≠ right.ptr.toNat + j

/-- Replaying a write to a disjoint byte range preserves an existing read
agreement. -/
theorem readEventReplayAgreement_of_writeMemoryOfEntry_disjoint
    {mem : Std.ExtHashMap Nat (BitVec 8)}
    {writeEntry readEntry : MemoryBusEntry FGL}
    (h_read :
      ReadEventReplayAgreement mem (eventOfEntry readEntry))
    (h_disjoint : MemoryBusEntryByteDisjoint readEntry writeEntry) :
    ReadEventReplayAgreement (writeMemoryOfEntry mem writeEntry)
      (eventOfEntry readEntry) := by
  unfold ReadEventReplayAgreement at h_read ⊢
  have h_write_ne_read :
      ∀ i j, i < 8 → j < 8 →
        writeEntry.ptr.toNat + j ≠ readEntry.ptr.toNat + i := by
    intro i j hi hj h_eq
    exact h_disjoint i j hi hj h_eq.symm
  have h_lookup :
      ∀ i, i < 8 →
        mem[readEntry.ptr.toNat + i]? = .some ((eventOfEntry readEntry).byteAt i) →
          (writeMemoryOfEntry mem writeEntry)[readEntry.ptr.toNat + i]? =
            .some ((eventOfEntry readEntry).byteAt i) := by
    intro i hi h_lane
    have h0 : writeEntry.ptr.toNat ≠ readEntry.ptr.toNat + i := by
      simpa using h_write_ne_read i 0 hi (by norm_num)
    have h1 : writeEntry.ptr.toNat + 1 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 1 hi (by norm_num)
    have h2 : writeEntry.ptr.toNat + 2 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 2 hi (by norm_num)
    have h3 : writeEntry.ptr.toNat + 3 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 3 hi (by norm_num)
    have h4 : writeEntry.ptr.toNat + 4 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 4 hi (by norm_num)
    have h5 : writeEntry.ptr.toNat + 5 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 5 hi (by norm_num)
    have h6 : writeEntry.ptr.toNat + 6 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 6 hi (by norm_num)
    have h7 : writeEntry.ptr.toNat + 7 ≠ readEntry.ptr.toNat + i :=
      h_write_ne_read i 7 hi (by norm_num)
    simp only [writeMemoryOfEntry, Std.ExtHashMap.getElem?_insert,
      beq_iff_eq, h0, h1, h2, h3, h4, h5, h6, h7]
    exact h_lane
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [eventOfEntry] using
      h_lookup 0 (by norm_num) (by simpa [eventOfEntry] using h_read.1)
  · simpa [eventOfEntry] using
      h_lookup 1 (by norm_num) (by simpa [eventOfEntry] using h_read.2.1)
  · simpa [eventOfEntry] using
      h_lookup 2 (by norm_num) (by simpa [eventOfEntry] using h_read.2.2.1)
  · simpa [eventOfEntry] using
      h_lookup 3 (by norm_num) (by simpa [eventOfEntry] using h_read.2.2.2.1)
  · simpa [eventOfEntry] using
      h_lookup 4 (by norm_num) (by simpa [eventOfEntry] using h_read.2.2.2.2.1)
  · simpa [eventOfEntry] using
      h_lookup 5 (by norm_num) (by simpa [eventOfEntry] using h_read.2.2.2.2.2.1)
  · simpa [eventOfEntry] using
      h_lookup 6 (by norm_num) (by simpa [eventOfEntry] using h_read.2.2.2.2.2.2.1)
  · simpa [eventOfEntry] using
      h_lookup 7 (by norm_num) (by simpa [eventOfEntry] using h_read.2.2.2.2.2.2.2)

/-- After preloading zero bytes at a row pointer, a zero-valued read at that
pointer is replay-sound. This is the first-read/address-change counterpart to
the write→read replay theorem. -/
theorem readEventReplayAgreement_of_zeroMemoryOfEntry
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {entry : MemoryBusEntry FGL}
    (h_value_0 : entry.value_0 = 0)
    (h_value_1 : entry.value_1 = 0) :
    ReadEventReplayAgreement (zeroMemoryOfEntry mem entry)
      (eventOfEntry entry) := by
  unfold zeroMemoryOfEntry
  apply readEventReplayAgreement_of_writeMemoryOfEntry_same
  · simp
  · simp [h_value_0]
  · simp [h_value_1]

/-- Zero-preloading a same-pointer row establishes a zero-valued read
agreement; zero-preloading a byte-disjoint row preserves an existing read
agreement. -/
theorem readEventReplayAgreement_of_zeroMemoryOfEntry_same_or_disjoint
    {mem : Std.ExtHashMap Nat (BitVec 8)}
    {row readEntry : MemoryBusEntry FGL}
    (h_read :
      ReadEventReplayAgreement mem (eventOfEntry readEntry))
    (h_value_0 : readEntry.value_0 = 0)
    (h_value_1 : readEntry.value_1 = 0)
    (h_same_or_disjoint :
      row.ptr = readEntry.ptr ∨ MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (zeroMemoryOfEntry mem row)
      (eventOfEntry readEntry) := by
  rcases h_same_or_disjoint with h_same | h_disjoint
  · unfold zeroMemoryOfEntry
    apply readEventReplayAgreement_of_writeMemoryOfEntry_same
    · simp [h_same]
    · simp [h_value_0]
    · simp [h_value_1]
  · unfold zeroMemoryOfEntry
    exact readEventReplayAgreement_of_writeMemoryOfEntry_disjoint
      h_read (by simpa [zeroedMemoryEntryOfEntry] using h_disjoint)

/-- Folding zero-preloads over rows that are either same-pointer or byte-
disjoint from a zero-valued read preserves the read agreement. -/
theorem readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_same_or_disjoint
    {mem : Std.ExtHashMap Nat (BitVec 8)}
    {rows : List (MemoryBusEntry FGL)}
    {readEntry : MemoryBusEntry FGL}
    (h_read :
      ReadEventReplayAgreement mem (eventOfEntry readEntry))
    (h_value_0 : readEntry.value_0 = 0)
    (h_value_1 : readEntry.value_1 = 0)
    (h_same_or_disjoint :
      ∀ row, row ∈ rows →
        row.ptr = readEntry.ptr ∨ MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (rows.foldl zeroMemoryOfEntry mem)
      (eventOfEntry readEntry) := by
  induction rows generalizing mem with
  | nil =>
      simpa using h_read
  | cons row rest ih =>
      have h_head :
          ReadEventReplayAgreement (zeroMemoryOfEntry mem row)
            (eventOfEntry readEntry) :=
        readEventReplayAgreement_of_zeroMemoryOfEntry_same_or_disjoint
          h_read h_value_0 h_value_1 (h_same_or_disjoint row (by simp))
      have h_tail :
          ∀ restRow, restRow ∈ rest →
            restRow.ptr = readEntry.ptr
              ∨ MemoryBusEntryByteDisjoint readEntry restRow := by
        intro restRow h_rest
        exact h_same_or_disjoint restRow (by simp [h_rest])
      simpa using ih h_head h_tail

/-- If a zero-preload fold contains the selected read entry, and every row in
the fold is either at the same pointer or byte-disjoint from it, then the final
preloaded memory satisfies the zero-valued read. -/
theorem readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_mem
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {rows : List (MemoryBusEntry FGL)}
    {readEntry : MemoryBusEntry FGL}
    (h_value_0 : readEntry.value_0 = 0)
    (h_value_1 : readEntry.value_1 = 0)
    (h_mem : readEntry ∈ rows)
    (h_same_or_disjoint :
      ∀ row, row ∈ rows →
        row.ptr = readEntry.ptr ∨ MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (rows.foldl zeroMemoryOfEntry mem)
      (eventOfEntry readEntry) := by
  induction rows generalizing mem with
  | nil =>
      simp at h_mem
  | cons row rest ih =>
      simp only [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_mem_tail
      · subst h_eq
        have h_start :
            ReadEventReplayAgreement (zeroMemoryOfEntry mem readEntry)
              (eventOfEntry readEntry) :=
          readEventReplayAgreement_of_zeroMemoryOfEntry mem h_value_0 h_value_1
        have h_tail :
            ∀ restRow, restRow ∈ rest →
              restRow.ptr = readEntry.ptr
                ∨ MemoryBusEntryByteDisjoint readEntry restRow := by
          intro restRow h_rest
          exact h_same_or_disjoint restRow (by simp [h_rest])
        simpa using
          readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_same_or_disjoint
            h_start h_value_0 h_value_1 h_tail
      · have h_tail :
            ∀ restRow, restRow ∈ rest →
              restRow.ptr = readEntry.ptr
                ∨ MemoryBusEntryByteDisjoint readEntry restRow := by
          intro restRow h_rest
          exact h_same_or_disjoint restRow (by simp [h_rest])
        simpa using
          ih (zeroMemoryOfEntry mem row) h_mem_tail h_tail

/-- Finite zero-preload memory for a row list satisfies any contained
zero-valued read whose other preloads are same-pointer or byte-disjoint. -/
theorem readEventReplayAgreement_of_zeroMemoryOfRows_mem
    {rows : List (MemoryBusEntry FGL)}
    {readEntry : MemoryBusEntry FGL}
    (h_value_0 : readEntry.value_0 = 0)
    (h_value_1 : readEntry.value_1 = 0)
    (h_mem : readEntry ∈ rows)
    (h_same_or_disjoint :
      ∀ row, row ∈ rows →
        row.ptr = readEntry.ptr ∨ MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (zeroMemoryOfRows rows)
      (eventOfEntry readEntry) := by
  exact readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_mem
    ({} : Std.ExtHashMap Nat (BitVec 8))
    h_value_0 h_value_1 h_mem h_same_or_disjoint

/-- If the zero-preload fold contains any row at the selected read's pointer,
then the preloaded memory satisfies a zero-valued read at that pointer. Other
preloads may target the same pointer or a byte-disjoint range. -/
theorem readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_same_ptr_mem
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {rows : List (MemoryBusEntry FGL)}
    {preloadEntry readEntry : MemoryBusEntry FGL}
    (h_value_0 : readEntry.value_0 = 0)
    (h_value_1 : readEntry.value_1 = 0)
    (h_mem : preloadEntry ∈ rows)
    (h_ptr : preloadEntry.ptr = readEntry.ptr)
    (h_same_or_disjoint :
      ∀ row, row ∈ rows →
        row.ptr = readEntry.ptr ∨ MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (rows.foldl zeroMemoryOfEntry mem)
      (eventOfEntry readEntry) := by
  induction rows generalizing mem with
  | nil =>
      simp at h_mem
  | cons row rest ih =>
      simp only [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_mem_tail
      · have h_row_ptr : row.ptr = readEntry.ptr := by
          simpa [h_eq] using h_ptr
        have h_start :
            ReadEventReplayAgreement (zeroMemoryOfEntry mem row)
              (eventOfEntry readEntry) := by
          unfold zeroMemoryOfEntry
          apply readEventReplayAgreement_of_writeMemoryOfEntry_same
          · simpa [zeroedMemoryEntryOfEntry] using h_row_ptr.symm
          · simpa [zeroedMemoryEntryOfEntry] using h_value_0
          · simpa [zeroedMemoryEntryOfEntry] using h_value_1
        have h_tail :
            ∀ restRow, restRow ∈ rest →
              restRow.ptr = readEntry.ptr
                ∨ MemoryBusEntryByteDisjoint readEntry restRow := by
          intro restRow h_rest
          exact h_same_or_disjoint restRow (by simp [h_rest])
        simpa using
          readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_same_or_disjoint
            h_start h_value_0 h_value_1 h_tail
      · have h_tail :
            ∀ restRow, restRow ∈ rest →
              restRow.ptr = readEntry.ptr
                ∨ MemoryBusEntryByteDisjoint readEntry restRow := by
          intro restRow h_rest
          exact h_same_or_disjoint restRow (by simp [h_rest])
        simpa using
          ih (zeroMemoryOfEntry mem row) h_mem_tail h_tail

/-- Finite zero-preload memory satisfies a zero-valued read when the preload
list contains any row at the read pointer and all other preloads are same-pointer
or byte-disjoint. -/
theorem readEventReplayAgreement_of_zeroMemoryOfRows_same_ptr_mem
    {rows : List (MemoryBusEntry FGL)}
    {preloadEntry readEntry : MemoryBusEntry FGL}
    (h_value_0 : readEntry.value_0 = 0)
    (h_value_1 : readEntry.value_1 = 0)
    (h_mem : preloadEntry ∈ rows)
    (h_ptr : preloadEntry.ptr = readEntry.ptr)
    (h_same_or_disjoint :
      ∀ row, row ∈ rows →
        row.ptr = readEntry.ptr ∨ MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (zeroMemoryOfRows rows)
      (eventOfEntry readEntry) := by
  exact readEventReplayAgreement_of_foldl_zeroMemoryOfEntry_same_ptr_mem
    ({} : Std.ExtHashMap Nat (BitVec 8))
    h_value_0 h_value_1 h_mem h_ptr h_same_or_disjoint

/-- Read replay agreement transports across memory-bus entries with the same
pointer and value chunks. -/
theorem readEventReplayAgreement_of_entry_same
    {mem : Std.ExtHashMap Nat (BitVec 8)}
    {sourceEntry targetEntry : MemoryBusEntry FGL}
    (h_read : ReadEventReplayAgreement mem (eventOfEntry sourceEntry))
    (h_ptr : targetEntry.ptr = sourceEntry.ptr)
    (h_value_0 : targetEntry.value_0 = sourceEntry.value_0)
    (h_value_1 : targetEntry.value_1 = sourceEntry.value_1) :
    ReadEventReplayAgreement mem (eventOfEntry targetEntry) := by
  cases sourceEntry
  cases targetEntry
  simp only at h_ptr h_value_0 h_value_1
  subst h_ptr
  subst h_value_0
  subst h_value_1
  simpa [ReadEventReplayAgreement, eventOfEntry, MemEvent.byteAt,
    ZiskFv.Channels.MemoryBusBytes.byteAt] using h_read

/-- A memory read event leaves Sail/replay memory agreement unchanged. -/
theorem eventReplayStep_read_entry_same_state
    (state : SailState) (e : MemoryBusEntry FGL) :
    EventReplayStep state state (eventOfEntry e) := by
  intro mem h_agree
  simpa [EventReplayStep, eventOfEntry] using h_agree

/-- An eight-lane memory write entry updates Sail memory and replay memory in
the same byte-addressed shape. -/
theorem replayMemoryAgreement_write_entry
    (before : SailState)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (e : MemoryBusEntry FGL)
    (h_agree : ReplayMemoryAgreement before mem) :
    ReplayMemoryAgreement
      { before with mem := writeMemoryOfEntry before.mem e }
      (replayStoreEvent mem (storeEventOfEntry e)) := by
  intro addr
  simp only [ReplayMemoryAgreement] at h_agree
  simp only [replayStoreEvent_storeEventOfEntry, writeMemoryOfEntry,
    Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  grind [h_agree addr]

/-- Updating Sail memory with `replayStoreEvent` preserves pointwise agreement
with a replay memory updated by the same event. This is the width-parametric
store transition used by accepted Mem trace replay. -/
theorem replayMemoryAgreement_replayStoreEvent
    (before : SailState)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (event : MemEvent)
    (h_agree : ReplayMemoryAgreement before mem) :
    ReplayMemoryAgreement
      { before with mem := replayStoreEvent before.mem event }
      (replayStoreEvent mem event) := by
  have h_mem_eq : before.mem = mem := by
    apply Std.ExtHashMap.ext_getElem?
    intro addr
    exact h_agree addr
  subst mem
  intro addr
  rfl

/-- Any Mem store event is an `EventReplayStep` when the post-state memory is
the width-parametric replay update of the pre-state memory. -/
theorem eventReplayStep_store_event_replay_state
    (before : SailState)
    (event : MemEvent)
    (h_store : event.op = (2 : FGL)) :
    EventReplayStep
      before
      { before with mem := replayStoreEvent before.mem event }
      event := by
  intro mem h_agree
  simp [h_store]
  exact replayMemoryAgreement_replayStoreEvent before mem event h_agree

/-- A memory-bus store entry is an `EventReplayStep` when the post-state is
the corresponding eight-lane Sail memory update. -/
theorem eventReplayStep_store_entry_write_state
    (before : SailState) (e : MemoryBusEntry FGL) :
    EventReplayStep
      before
      { before with mem := writeMemoryOfEntry before.mem e }
      (storeEventOfEntry e) := by
  intro mem h_agree
  simpa [EventReplayStep, storeEventOfEntry] using
    replayMemoryAgreement_write_entry before mem e h_agree

/-- Chronological memory-bus events used by the execution replay bridge.
Reads are selected load events; writes are the eight-lane memory-bus writes
that `bus_effect` applies to Sail memory. -/
inductive MemoryBusTraceEvent where
  | read (entry : MemoryBusEntry FGL)
  | write (entry : MemoryBusEntry FGL)

namespace MemoryBusTraceEvent

/-- Convert a chronological memory-bus event to the Mem replay event. -/
@[reducible]
def toMemEvent : MemoryBusTraceEvent → MemEvent
  | .read entry => eventOfEntry entry
  | .write entry => storeEventOfEntry entry

/-- Apply one chronological memory-bus event to Sail state memory. -/
@[reducible]
def applyState (state : SailState) : MemoryBusTraceEvent → SailState
  | .read _entry => state
  | .write entry => { state with mem := writeMemoryOfEntry state.mem entry }

/-- Every concrete memory-bus event is a valid replay step for the state
transition produced by `applyState`. -/
theorem eventReplayStep
    (state : SailState) (event : MemoryBusTraceEvent) :
    EventReplayStep state (event.applyState state) event.toMemEvent := by
  cases event with
  | read entry =>
      simpa [toMemEvent, applyState] using
        eventReplayStep_read_entry_same_state state entry
  | write entry =>
      simpa [toMemEvent, applyState] using
        eventReplayStep_store_entry_write_state state entry

end MemoryBusTraceEvent

/-- The Mem trace obtained from a chronological memory-bus event list. -/
@[reducible]
def memoryBusTraceEventsToMemTrace
    (events : List MemoryBusTraceEvent) : List MemEvent :=
  events.map MemoryBusTraceEvent.toMemEvent

/-- Project a legacy memory-bus row into a chronological memory replay event.
    Only memory-address-space rows with active read/write multiplicity
    participate in memory replay; register-space and no-effect rows are
    ignored. -/
@[reducible]
def memoryBusTraceEventOfRow
    (entry : MemoryBusEntry FGL) : Option MemoryBusTraceEvent :=
  if entry.as = (2 : FGL) then
    if entry.multiplicity = (-1 : FGL) then
      some (MemoryBusTraceEvent.read entry)
    else if entry.multiplicity = (1 : FGL) then
      some (MemoryBusTraceEvent.write entry)
    else
      none
  else
    none

/-- Chronological memory replay events projected from raw memory-bus rows. -/
@[reducible]
def memoryBusTraceEventsOfRows
    (rows : List (MemoryBusEntry FGL)) : List MemoryBusTraceEvent :=
  rows.filterMap memoryBusTraceEventOfRow

/-- Replay memory after one raw memory-bus row. Only active memory writes
    update replay memory; reads, inactive rows, and non-memory rows leave it
    unchanged. -/
@[reducible]
def replayMemoryAfterBusRow
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (row : MemoryBusEntry FGL) :
    Std.ExtHashMap Nat (BitVec 8) :=
  if row.as = (2 : FGL) then
    if row.multiplicity = (1 : FGL) then
      replayStoreEvent mem (storeEventOfEntry row)
    else
      mem
  else
    mem

/-- A selected read memory-bus row does not mutate replay memory. -/
theorem replayMemoryAfterBusRow_eq_self_of_read
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (entry : MemoryBusEntry FGL)
    (h_as : entry.as = (2 : FGL))
    (h_read : entry.multiplicity = (-1 : FGL)) :
    replayMemoryAfterBusRow mem entry = mem := by
  have h_not_write : ¬entry.multiplicity = (1 : FGL) := by
    intro h_write
    have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
      native_decide
    exact h_one_ne_neg_one (h_write.symm.trans h_read)
  simp [replayMemoryAfterBusRow, h_as, h_not_write]

/-- Replay memory after a chronological prefix of raw memory-bus rows. -/
@[reducible]
def replayMemoryAfterBusRows
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (MemoryBusEntry FGL)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  rows.foldl replayMemoryAfterBusRow mem

/-- Replaying one raw memory-bus row preserves a read agreement when any write
effect of that row targets a disjoint eight-byte range. Non-write rows preserve
the agreement definitionally. -/
theorem readEventReplayAgreement_of_replayMemoryAfterBusRow_disjoint
    {mem : Std.ExtHashMap Nat (BitVec 8)}
    {row readEntry : MemoryBusEntry FGL}
    (h_read :
      ReadEventReplayAgreement mem (eventOfEntry readEntry))
    (h_disjoint : MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (replayMemoryAfterBusRow mem row)
      (eventOfEntry readEntry) := by
  by_cases h_as : row.as = (2 : FGL)
  · by_cases h_write : row.multiplicity = (1 : FGL)
    · simpa [replayMemoryAfterBusRow, h_as, h_write,
        replayStoreEvent_storeEventOfEntry] using
        readEventReplayAgreement_of_writeMemoryOfEntry_disjoint h_read h_disjoint
    · simpa [replayMemoryAfterBusRow, h_as, h_write] using h_read
  · simpa [replayMemoryAfterBusRow, h_as] using h_read

/-- Replaying a prefix of raw memory-bus rows preserves a read agreement when
all rows in the prefix are byte-disjoint from the read entry. -/
theorem readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
    {mem : Std.ExtHashMap Nat (BitVec 8)}
    {rows : List (MemoryBusEntry FGL)}
    {readEntry : MemoryBusEntry FGL}
    (h_read :
      ReadEventReplayAgreement mem (eventOfEntry readEntry))
    (h_disjoint :
      ∀ row, row ∈ rows → MemoryBusEntryByteDisjoint readEntry row) :
    ReadEventReplayAgreement (replayMemoryAfterBusRows mem rows)
      (eventOfEntry readEntry) := by
  induction rows generalizing mem with
  | nil =>
      simpa [replayMemoryAfterBusRows] using h_read
  | cons row rest ih =>
      have h_head :
          ReadEventReplayAgreement (replayMemoryAfterBusRow mem row)
            (eventOfEntry readEntry) :=
        readEventReplayAgreement_of_replayMemoryAfterBusRow_disjoint
          h_read (h_disjoint row (by simp))
      have h_tail :
          ∀ restRow, restRow ∈ rest →
            MemoryBusEntryByteDisjoint readEntry restRow := by
        intro restRow h_rest
        exact h_disjoint restRow (by simp [h_rest])
      simpa [replayMemoryAfterBusRows] using ih h_head h_tail

/-- Replaying raw memory-bus rows is the same memory update as replaying their
    projected read/write event list. This lets AIR-facing proofs reason over
    raw rows while the existing load bridge continues to consume Mem events. -/
theorem replayMemoryAfterBusRows_eq_replayEvents
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (MemoryBusEntry FGL)) :
    replayMemoryAfterBusRows mem rows =
      replayEvents mem
        (memoryBusTraceEventsToMemTrace (memoryBusTraceEventsOfRows rows)) := by
  induction rows generalizing mem with
  | nil =>
      simp [replayMemoryAfterBusRows, memoryBusTraceEventsOfRows,
        memoryBusTraceEventsToMemTrace, replayEvents]
  | cons row rest ih =>
      by_cases h_as : row.as = (2 : FGL)
      · by_cases h_read : row.multiplicity = (-1 : FGL)
        · have h_event :
            memoryBusTraceEventOfRow row =
              some (MemoryBusTraceEvent.read row) := by
              simp [memoryBusTraceEventOfRow, h_as, h_read]
          have h_row_replay :
              replayMemoryAfterBusRow mem row = mem := by
            have h_not_write : ¬row.multiplicity = (1 : FGL) := by
              intro h_write
              have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
                native_decide
              exact h_one_ne_neg_one (h_write.symm.trans h_read)
            simp [replayMemoryAfterBusRow, h_as, h_not_write]
          simpa [replayMemoryAfterBusRows, memoryBusTraceEventsOfRows,
            memoryBusTraceEventsToMemTrace, replayEvents, h_event,
            MemoryBusTraceEvent.toMemEvent, h_row_replay] using ih mem
        · by_cases h_write : row.multiplicity = (1 : FGL)
          · have h_event :
              memoryBusTraceEventOfRow row =
                some (MemoryBusTraceEvent.write row) := by
              have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
                native_decide
              simp [memoryBusTraceEventOfRow, h_as, h_write,
                h_one_ne_neg_one]
            have h_row_replay :
                replayMemoryAfterBusRow mem row =
                  replayStoreEvent mem (storeEventOfEntry row) := by
              simp [replayMemoryAfterBusRow, h_as, h_write]
            simpa [replayMemoryAfterBusRows, memoryBusTraceEventsOfRows,
              memoryBusTraceEventsToMemTrace, replayEvents, h_event,
              MemoryBusTraceEvent.toMemEvent, storeEventOfEntry,
              h_row_replay] using
              ih (replayStoreEvent mem (storeEventOfEntry row))
          · have h_event : memoryBusTraceEventOfRow row = none := by
              simp [memoryBusTraceEventOfRow, h_as, h_read, h_write]
            have h_row_replay :
                replayMemoryAfterBusRow mem row = mem := by
              simp [replayMemoryAfterBusRow, h_as, h_write]
            simpa [replayMemoryAfterBusRows, memoryBusTraceEventsOfRows,
              memoryBusTraceEventsToMemTrace, h_event, h_row_replay] using
              ih mem
      · have h_event : memoryBusTraceEventOfRow row = none := by
          simp [memoryBusTraceEventOfRow, h_as]
        have h_row_replay :
            replayMemoryAfterBusRow mem row = mem := by
          simp [replayMemoryAfterBusRow, h_as]
        simpa [replayMemoryAfterBusRows, memoryBusTraceEventsOfRows,
          memoryBusTraceEventsToMemTrace, h_event, h_row_replay] using ih mem

/-- Row-level global replay soundness for chronological raw memory-bus rows.

For every active memory read row, the emitted value must equal the replay
memory at that row's pointer. Active memory write rows update the replay
memory in the same eight-byte shape as `bus_effect`; all other rows are
ignored for memory replay. -/
def MemoryBusRowsReadWriteSound :
    Std.ExtHashMap Nat (BitVec 8) →
      List (MemoryBusEntry FGL) → Prop
  | _mem, [] => True
  | mem, row :: rest =>
      (row.as = (2 : FGL) →
        row.multiplicity = (-1 : FGL) →
          ReadEventReplayAgreement mem (eventOfEntry row))
      ∧ MemoryBusRowsReadWriteSound
          (replayMemoryAfterBusRow mem row) rest

/-- Prefix-indexed read soundness for chronological raw memory-bus rows.

This is the shape expected from accepted AIR trace data: for every selected
read row in the chronological list, the row's emitted value agrees with the
memory obtained by replaying the preceding rows. -/
def MemoryBusRowsPrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (MemoryBusEntry FGL)) : Prop :=
  ∀ priorRows row laterRows,
    rows = priorRows ++ row :: laterRows →
      row.as = (2 : FGL) →
        row.multiplicity = (-1 : FGL) →
          ReadEventReplayAgreement
            (replayMemoryAfterBusRows initialMemory priorRows)
            (eventOfEntry row)

/-- Prefix-indexed read soundness implies the recursive row-level replay
    predicate consumed by the memory-bus trace bridge. -/
theorem memoryBusRowsReadWriteSound_of_prefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (MemoryBusEntry FGL))
    (h_prefix : MemoryBusRowsPrefixReadSound initialMemory rows) :
    MemoryBusRowsReadWriteSound initialMemory rows := by
  induction rows generalizing initialMemory with
  | nil =>
      simp [MemoryBusRowsReadWriteSound]
  | cons row rest ih =>
      simp only [MemoryBusRowsReadWriteSound]
      constructor
      · intro h_as h_mult
        exact h_prefix [] row rest (by simp) h_as h_mult
      · apply ih
        intro priorRows selectedRow laterRows h_split h_as h_mult
        have h_rows_split :
            row :: rest = (row :: priorRows) ++ selectedRow :: laterRows := by
          simp [h_split]
        have h_selected :=
          h_prefix (row :: priorRows) selectedRow laterRows
            h_rows_split h_as h_mult
        simpa [replayMemoryAfterBusRows] using h_selected

/-- Recursive row-level replay soundness implies the prefix-indexed read
    form. This lets accepted Mem trace construction discharge read soundness
    either by a direct prefix theorem or by a sequential replay proof over the
    chronological rows. -/
theorem memoryBusRowsPrefixReadSound_of_readWriteSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (MemoryBusEntry FGL))
    (h_rows : MemoryBusRowsReadWriteSound initialMemory rows) :
    MemoryBusRowsPrefixReadSound initialMemory rows := by
  intro priorRows selectedRow laterRows h_split h_as h_mult
  induction priorRows generalizing initialMemory rows with
  | nil =>
      subst rows
      simpa [MemoryBusRowsReadWriteSound] using h_rows.1 h_as h_mult
  | cons row priorRows ih =>
      cases rows with
      | nil =>
          simp at h_split
      | cons head rest =>
          simp only [List.cons_append, List.cons.injEq] at h_split
          obtain ⟨h_head, h_rest⟩ := h_split
          subst head
          have h_tail : MemoryBusRowsReadWriteSound
              (replayMemoryAfterBusRow initialMemory row) rest := by
            simpa [MemoryBusRowsReadWriteSound] using h_rows.2
          have h_selected :=
            ih (replayMemoryAfterBusRow initialMemory row) rest
              h_tail h_rest
          simpa [replayMemoryAfterBusRows] using h_selected

@[simp]
theorem replayMemoryAfterBusRows_append
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (xs ys : List (MemoryBusEntry FGL)) :
    replayMemoryAfterBusRows mem (xs ++ ys) =
      replayMemoryAfterBusRows (replayMemoryAfterBusRows mem xs) ys := by
  simp [replayMemoryAfterBusRows, List.foldl_append]

/-- Recursive read/write soundness composes across list append when the suffix
    starts from the replay memory produced by the prefix. -/
theorem memoryBusRowsReadWriteSound_append
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (xs ys : List (MemoryBusEntry FGL))
    (h_xs : MemoryBusRowsReadWriteSound initialMemory xs)
    (h_ys :
      MemoryBusRowsReadWriteSound
        (replayMemoryAfterBusRows initialMemory xs) ys) :
    MemoryBusRowsReadWriteSound initialMemory (xs ++ ys) := by
  induction xs generalizing initialMemory with
  | nil =>
      simpa [replayMemoryAfterBusRows] using h_ys
  | cons row rest ih =>
      simp only [List.cons_append, MemoryBusRowsReadWriteSound] at h_xs ⊢
      constructor
      · exact h_xs.1
      · exact
          ih (replayMemoryAfterBusRow initialMemory row) h_xs.2
            (by simpa [replayMemoryAfterBusRows] using h_ys)

/-- Prefix read soundness composes across list append when the suffix is proved
    against the replay memory produced by the prefix. -/
theorem memoryBusRowsPrefixReadSound_append
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (xs ys : List (MemoryBusEntry FGL))
    (h_xs : MemoryBusRowsPrefixReadSound initialMemory xs)
    (h_ys :
      MemoryBusRowsPrefixReadSound
        (replayMemoryAfterBusRows initialMemory xs) ys) :
    MemoryBusRowsPrefixReadSound initialMemory (xs ++ ys) := by
  exact memoryBusRowsPrefixReadSound_of_readWriteSound initialMemory (xs ++ ys)
    (memoryBusRowsReadWriteSound_append initialMemory xs ys
      (memoryBusRowsReadWriteSound_of_prefixReadSound initialMemory xs h_xs)
      (memoryBusRowsReadWriteSound_of_prefixReadSound
        (replayMemoryAfterBusRows initialMemory xs) ys h_ys))

@[simp]
lemma memoryBusTraceEventOfRow_read
    (entry : MemoryBusEntry FGL)
    (h_as : entry.as = (2 : FGL))
    (h_mult : entry.multiplicity = (-1 : FGL)) :
    memoryBusTraceEventOfRow entry =
      some (MemoryBusTraceEvent.read entry) := by
  simp [memoryBusTraceEventOfRow, h_as, h_mult]

/-- Invert the selected-read projection of a raw memory-bus row. -/
theorem read_tags_of_memoryBusTraceEventOfRow_read
    (entry : MemoryBusEntry FGL)
    (h_read :
      memoryBusTraceEventOfRow entry =
        some (MemoryBusTraceEvent.read entry)) :
    entry.as = (2 : FGL) ∧ entry.multiplicity = (-1 : FGL) := by
  unfold memoryBusTraceEventOfRow at h_read
  by_cases h_as : entry.as = (2 : FGL)
  · by_cases h_mult : entry.multiplicity = (-1 : FGL)
    · exact ⟨h_as, h_mult⟩
    · simp [h_as, h_mult] at h_read
  · simp [h_as] at h_read

@[simp]
lemma memoryBusTraceEventsOfRows_append
    (xs ys : List (MemoryBusEntry FGL)) :
    memoryBusTraceEventsOfRows (xs ++ ys) =
      memoryBusTraceEventsOfRows xs ++ memoryBusTraceEventsOfRows ys := by
  simp [memoryBusTraceEventsOfRows]

/-- Row-level replay soundness implies the event-level `TraceReplaySound`
    consumed by selected-load proofs. -/
theorem traceReplaySound_of_memoryBusRowsReadWriteSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rows : List (MemoryBusEntry FGL))
    (h_rows : MemoryBusRowsReadWriteSound initialMemory rows) :
    TraceReplaySound initialMemory
      (memoryBusTraceEventsToMemTrace (memoryBusTraceEventsOfRows rows)) := by
  induction rows generalizing initialMemory with
  | nil =>
      simp [memoryBusTraceEventsOfRows, memoryBusTraceEventsToMemTrace,
        TraceReplaySound]
  | cons row rest ih =>
      simp only [MemoryBusRowsReadWriteSound] at h_rows
      by_cases h_as : row.as = (2 : FGL)
      · by_cases h_read : row.multiplicity = (-1 : FGL)
        · have h_event :
            memoryBusTraceEventOfRow row =
              some (MemoryBusTraceEvent.read row) := by
              simp [memoryBusTraceEventOfRow, h_as, h_read]
          have h_tail :
              TraceReplaySound initialMemory
                (memoryBusTraceEventsToMemTrace
                  (memoryBusTraceEventsOfRows rest)) :=
            ih initialMemory
              (by
                simpa [replayMemoryAfterBusRow, h_as, h_read] using
                  h_rows.2)
          simp [memoryBusTraceEventsOfRows, memoryBusTraceEventsToMemTrace,
            h_event, TraceReplaySound, MemoryBusTraceEvent.toMemEvent,
            eventOfEntry, h_rows.1 h_as h_read, h_tail]
        · by_cases h_write : row.multiplicity = (1 : FGL)
          · have h_event :
              memoryBusTraceEventOfRow row =
                some (MemoryBusTraceEvent.write row) := by
                have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
                  native_decide
                simp [memoryBusTraceEventOfRow, h_as, h_write,
                  h_one_ne_neg_one]
            have h_rows_tail :
                MemoryBusRowsReadWriteSound
                  (replayStoreEvent initialMemory (storeEventOfEntry row))
                  rest := by
              simpa [replayMemoryAfterBusRow, h_as, h_write] using
                h_rows.2
            have h_tail :=
              ih (replayStoreEvent initialMemory (storeEventOfEntry row))
                h_rows_tail
            simpa [memoryBusTraceEventsOfRows, memoryBusTraceEventsToMemTrace,
              h_event, TraceReplaySound, MemoryBusTraceEvent.toMemEvent,
              storeEventOfEntry, replayStoreEvent_storeEventOfEntry] using
              h_tail
          · have h_event : memoryBusTraceEventOfRow row = none := by
              simp [memoryBusTraceEventOfRow, h_as, h_read, h_write]
            have h_tail :
                TraceReplaySound initialMemory
                  (memoryBusTraceEventsToMemTrace
                    (memoryBusTraceEventsOfRows rest)) :=
              ih initialMemory
                (by
                  simpa [replayMemoryAfterBusRow, h_as, h_write] using
                    h_rows.2)
            simpa [memoryBusTraceEventsOfRows, memoryBusTraceEventsToMemTrace,
              h_event, replayMemoryAfterBusRow, h_as, h_write] using
              h_tail
      · have h_event : memoryBusTraceEventOfRow row = none := by
          simp [memoryBusTraceEventOfRow, h_as]
        have h_tail :
            TraceReplaySound initialMemory
              (memoryBusTraceEventsToMemTrace
                (memoryBusTraceEventsOfRows rest)) :=
          ih initialMemory
            (by
              simpa [replayMemoryAfterBusRow, h_as] using h_rows.2)
        simpa [memoryBusTraceEventsOfRows, memoryBusTraceEventsToMemTrace,
          h_event, replayMemoryAfterBusRow, h_as] using h_tail

/-- Sail state after applying a chronological list of memory-bus events. -/
@[reducible]
def stateAfterMemoryBusTrace
    (initial : SailState) (events : List MemoryBusTraceEvent) : SailState :=
  events.foldl
    (fun state event => MemoryBusTraceEvent.applyState state event)
    initial

/-- Sail state after applying the read/write projection of chronological raw
    memory-bus rows. -/
@[reducible]
def stateAfterMemoryBusRows
    (initial : SailState) (rows : List (MemoryBusEntry FGL)) : SailState :=
  stateAfterMemoryBusTrace initial (memoryBusTraceEventsOfRows rows)

/-- Replaying a chronological memory-bus prefix preserves Sail/replay memory
agreement. -/
theorem replayAgreement_after_memoryBusTrace
    (initial : SailState)
    (events : List MemoryBusTraceEvent)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (h_initial : ReplayMemoryAgreement initial mem) :
    ReplayMemoryAgreement
      (stateAfterMemoryBusTrace initial events)
      (replayEvents mem (memoryBusTraceEventsToMemTrace events)) := by
  induction events generalizing initial mem with
  | nil =>
      simpa [stateAfterMemoryBusTrace, memoryBusTraceEventsToMemTrace,
        replayEvents] using h_initial
  | cons event rest ih =>
      have h_step :
          ReplayMemoryAgreement
            (MemoryBusTraceEvent.applyState initial event)
            (if event.toMemEvent.op = (2 : FGL) then
              replayStoreEvent mem event.toMemEvent
            else
              mem) :=
        MemoryBusTraceEvent.eventReplayStep initial event mem h_initial
      have h_tail :=
        ih (MemoryBusTraceEvent.applyState initial event)
          (if event.toMemEvent.op = (2 : FGL) then
            replayStoreEvent mem event.toMemEvent
          else
            mem)
          h_step
      simpa [stateAfterMemoryBusTrace, memoryBusTraceEventsToMemTrace,
        replayEvents] using h_tail

/-- Replaying a chronological raw memory-bus row prefix preserves Sail/replay
    memory agreement in the raw-row replay model. -/
theorem replayAgreement_after_memoryBusRows
    (initial : SailState)
    (rows : List (MemoryBusEntry FGL))
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (h_initial : ReplayMemoryAgreement initial mem) :
    ReplayMemoryAgreement
      (stateAfterMemoryBusRows initial rows)
      (replayMemoryAfterBusRows mem rows) := by
  rw [replayMemoryAfterBusRows_eq_replayEvents]
  exact
    replayAgreement_after_memoryBusTrace
      initial (memoryBusTraceEventsOfRows rows) mem h_initial

/-- Accepted memory-replay evidence for the chronological memory-bus rows.

This is the circuit-side table/replay obligation: the accepted row list is the
memory timeline whose read rows agree with replayed prior writes. Once the
concrete Mem-table proof is assembled, this object should be constructed from
the extracted Mem AIR constraints instead of carried by the residual boundary. -/
structure AcceptedMemoryReplayEvidence : Type where
  rows : List (MemoryBusEntry FGL)
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  prefixReadSound : MemoryBusRowsPrefixReadSound initialMemory rows

/-- Residual Sail-memory timeline evidence for one selected load.

`acceptedReplay` is the named circuit-side replay obligation. The remaining
fields carry the execution-timeline boundary: the selected read is located in
the accepted row list, the initial Sail memory agrees with the replay memory,
and the selected Sail state is the state obtained by replaying the accepted
prefix before the selected read row. -/
structure MemoryTimelineEvidence
    (state : SailState)
    (entry : MemoryBusEntry FGL) : Type where
  initialState : SailState
  acceptedReplay : AcceptedMemoryReplayEvidence
  priorRows : List (MemoryBusEntry FGL)
  laterRows : List (MemoryBusEntry FGL)
  traceSplit : acceptedReplay.rows = priorRows ++ entry :: laterRows
  selectedRead :
    memoryBusTraceEventOfRow entry = some (MemoryBusTraceEvent.read entry)
  initialAgreement :
    ReplayMemoryAgreement initialState acceptedReplay.initialMemory
  stateAtPrefix : state = stateAfterMemoryBusRows initialState priorRows

/-- Timeline evidence gives replay agreement for the selected read row at its
accepted chronological prefix. -/
theorem MemoryTimelineEvidence.prefixReadAgreement
    {state : SailState}
    {entry : MemoryBusEntry FGL}
    (evidence : MemoryTimelineEvidence state entry) :
    ReadEventReplayAgreement
      (replayMemoryAfterBusRows evidence.acceptedReplay.initialMemory evidence.priorRows)
      (eventOfEntry entry) := by
  obtain ⟨h_as, h_mult⟩ :=
    read_tags_of_memoryBusTraceEventOfRow_read
      entry evidence.selectedRead
  exact
    evidence.acceptedReplay.prefixReadSound
      evidence.priorRows entry evidence.laterRows
      evidence.traceSplit h_as h_mult

/-- Timeline evidence gives Sail/replay memory agreement at the selected
prefix cursor. -/
theorem MemoryTimelineEvidence.prefixStateAgreement
    {state : SailState}
    {entry : MemoryBusEntry FGL}
    (evidence : MemoryTimelineEvidence state entry) :
    ReplayMemoryAgreement
      state
      (replayMemoryAfterBusRows evidence.acceptedReplay.initialMemory evidence.priorRows) := by
  rcases evidence with
    ⟨initialState, acceptedReplay, priorRows, laterRows, traceSplit,
      selectedRead, initialAgreement, stateAtPrefix⟩
  subst state
  exact
    replayAgreement_after_memoryBusRows
      initialState priorRows acceptedReplay.initialMemory initialAgreement

/-- The residual timeline evidence plus circuit-side prefix read soundness
imply the selected load byte agreement shape used by local load correctness. -/
theorem MemoryTimelineEvidence.memoryTraceAgreement
    {state : SailState}
    {entry : MemoryBusEntry FGL}
    (evidence : MemoryTimelineEvidence state entry) :
    MemoryTraceAgreement state (eventOfEntry entry) :=
  memoryTraceAgreement_of_replayAgreement
    state
    (replayMemoryAfterBusRows evidence.acceptedReplay.initialMemory evidence.priorRows)
    (eventOfEntry entry)
    evidence.prefixStateAgreement
    evidence.prefixReadAgreement

/-- Agreement for `eventOfEntry e` is exactly the byte facts expected by
`bus_effect` load consumers. -/
lemma byte_facts_of_event_agreement
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (e : MemoryBusEntry FGL)
    (h : MemoryTraceAgreement state (eventOfEntry e)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)
    ∧ state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4)
    ∧ state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5)
    ∧ state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6)
    ∧ state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7) := by
  simpa [MemoryTraceAgreement, eventOfEntry_byteAt] using h

end ZiskFv.ZiskCircuit.MemTrace
