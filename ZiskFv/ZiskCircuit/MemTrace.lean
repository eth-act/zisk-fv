import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.SailSpec.Auxiliaries

/-!
# Mem trace vocabulary

This module contains the theorem-shaped replacement vocabulary for the
load-side Sail memory bridge.  The local load theorem in `MemModel` no
longer quantifies over an arbitrary Sail state; it consumes an explicit
agreement fact between the selected memory event and that state's byte map.

The replay/global construction layer is intentionally separated from the
local load projection layer: whole-trace soundness should prove
`MemoryTraceAgreement` for selected read events from accepted trace data and
initial memory agreement, while opcode wrappers only consume the selected
agreement fact.
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

/-- Accepted Mem trace facts needed by load soundness. This is the explicit
nonlocal proof boundary: future Mem AIR work should derive `traceSound`
from full Mem trace continuity constraints and accepted store replay. -/
structure AcceptedMemTrace
    (trace : List MemEvent) : Type where
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  storeReplaySound : Prop
  eventOrderingSound : Prop
  segmentCarrySound : Prop
  dualEventsSound : Prop
  traceSound : TraceReplaySound initialMemory trace

/-- Accepted Mem trace plus Sail/replay cursor agreement for read events in
that trace.

This is the reusable global memory object: it carries one accepted replay
trace for the current Sail state, and states that every selected read cursor
in that trace agrees with the Sail byte map. Opcode-level load proofs still
have to prove that their selected memory-bus event occurs in this trace. -/
structure AcceptedMemTraceForState
    (state : SailState)
    (trace : List MemEvent) : Type where
  accepted : AcceptedMemTrace trace
  readCursorAgreement :
    ∀ (event : MemEvent) (priorEvents laterEvents : List MemEvent),
      trace = priorEvents ++ event :: laterEvents →
      event.op = (1 : FGL) →
      ReplayMemoryAgreement state
        (replayEvents accepted.initialMemory priorEvents)

/-- Accepted Mem trace plus a Sail execution-state function whose memory
    transitions replay the trace. -/
structure AcceptedExecutionMemoryTrace
    (stateAt : List MemEvent → SailState)
    (trace : List MemEvent) : Type where
  accepted : AcceptedMemTrace trace
  initialAgreement :
    ReplayMemoryAgreement (stateAt []) accepted.initialMemory
  replaySteps : PrefixReplayStepsFrom stateAt [] trace

/-- Cursor agreement for any prefix of an accepted execution memory trace. -/
theorem replayAgreement_at_prefix_of_execution_trace
    (stateAt : List MemEvent → SailState)
    (trace priorEvents laterEvents : List MemEvent)
    (execTrace : AcceptedExecutionMemoryTrace stateAt trace)
    (h_split : trace = priorEvents ++ laterEvents) :
    ReplayMemoryAgreement (stateAt priorEvents)
      (replayEvents execTrace.accepted.initialMemory priorEvents) := by
  have h_steps :
      PrefixReplayStepsFrom stateAt [] priorEvents :=
    prefixReplayStepsFrom_of_append stateAt [] priorEvents laterEvents
      (by simpa [h_split] using execTrace.replaySteps)
  simpa using
    replayAgreement_of_prefixReplayStepsFrom stateAt [] priorEvents
      execTrace.accepted.initialMemory execTrace.initialAgreement h_steps

/-- Selected load event plus the accepted trace facts from which its Sail
memory agreement is derived. -/
structure LoadTraceContext
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent) : Type where
  trace : List MemEvent
  accepted : AcceptedMemTrace trace
  priorEvents : List MemEvent
  laterEvents : List MemEvent
  trace_split : trace = priorEvents ++ event :: laterEvents
  read : event.op = (1 : FGL)
  stateReplayAgreement :
    ReplayMemoryAgreement state (replayEvents accepted.initialMemory priorEvents)

/-- Public load-memory burden for a selected event. Unlike
`LoadTraceContext`, this is a proposition that callers can prove from a
top-level accepted Mem trace without first packing the evidence into a load
promise constructor. -/
def LoadMemoryBurden
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent) : Prop :=
  ∃ trace : List MemEvent,
  ∃ accepted : AcceptedMemTrace trace,
  ∃ priorEvents : List MemEvent,
  ∃ laterEvents : List MemEvent,
    trace = priorEvents ++ event :: laterEvents
    ∧ event.op = (1 : FGL)
    ∧ ReplayMemoryAgreement state (replayEvents accepted.initialMemory priorEvents)

/-- Derive a selected load burden from the shared accepted trace object and
membership of the selected event in that trace. -/
theorem loadMemoryBurden_of_accepted_trace_for_state
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent)
    (trace : List MemEvent)
    (ctx : AcceptedMemTraceForState state trace)
    (priorEvents laterEvents : List MemEvent)
    (h_split : trace = priorEvents ++ event :: laterEvents)
    (h_read : event.op = (1 : FGL)) :
    LoadMemoryBurden state event := by
  exact ⟨trace, ctx.accepted, priorEvents, laterEvents, h_split, h_read,
    ctx.readCursorAgreement event priorEvents laterEvents h_split h_read⟩

/-- Existential membership-shaped version used by `OpEnvelope` load arms. -/
theorem loadMemoryBurden_of_accepted_trace_membership
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent)
    (h_membership :
      ∃ trace : List MemEvent,
      ∃ _ctx : AcceptedMemTraceForState state trace,
      ∃ priorEvents : List MemEvent,
      ∃ laterEvents : List MemEvent,
        trace = priorEvents ++ event :: laterEvents)
    (h_read : event.op = (1 : FGL)) :
    LoadMemoryBurden state event := by
  rcases h_membership with
    ⟨trace, ctx, priorEvents, laterEvents, h_split⟩
  exact loadMemoryBurden_of_accepted_trace_for_state
    state event trace ctx priorEvents laterEvents h_split h_read

/-- Simplified membership shape produced when the shared accepted-trace
context is normalized around a selected load event. -/
theorem loadMemoryBurden_of_accepted_trace_split_nonempty
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent)
    (h_membership :
      ∃ priorEvents : List MemEvent,
      ∃ laterEvents : List MemEvent,
        Nonempty
          (AcceptedMemTraceForState state
            (priorEvents ++ event :: laterEvents)))
    (h_read : event.op = (1 : FGL)) :
    LoadMemoryBurden state event := by
  rcases h_membership with
    ⟨priorEvents, laterEvents, ⟨ctx⟩⟩
  exact loadMemoryBurden_of_accepted_trace_for_state
    state event (priorEvents ++ event :: laterEvents) ctx
    priorEvents laterEvents rfl h_read

/-- The local load byte agreement obtained from the accepted Mem trace
context. -/
theorem memoryTraceAgreement_of_load_context
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent)
    (ctx : LoadTraceContext state event) :
    MemoryTraceAgreement state event :=
  by
    have h_read :=
      readEventReplayAgreement_of_trace_sound
        ctx.accepted.initialMemory ctx.priorEvents event ctx.laterEvents
        (by simpa [ctx.trace_split] using ctx.accepted.traceSound)
        ctx.read
    unfold MemoryTraceAgreement
    unfold ReadEventReplayAgreement at h_read
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ctx.stateReplayAgreement event.ptr.toNat]
      exact h_read.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 1)]
      exact h_read.2.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 2)]
      exact h_read.2.2.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 3)]
      exact h_read.2.2.2.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 4)]
      exact h_read.2.2.2.2.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 5)]
      exact h_read.2.2.2.2.2.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 6)]
      exact h_read.2.2.2.2.2.2.1
    · rw [ctx.stateReplayAgreement (event.ptr.toNat + 7)]
      exact h_read.2.2.2.2.2.2.2

/-- The selected load byte agreement obtained from the public load-memory
burden. -/
theorem memoryTraceAgreement_of_load_memory_burden
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent)
    (h_burden : LoadMemoryBurden state event) :
    MemoryTraceAgreement state event :=
  by
    rcases h_burden with
      ⟨trace, accepted, priorEvents, laterEvents,
        h_trace_split, h_read_event, h_state_replay⟩
    have h_read :=
      readEventReplayAgreement_of_trace_sound
        accepted.initialMemory priorEvents event laterEvents
        (by simpa [h_trace_split] using accepted.traceSound)
        h_read_event
    unfold MemoryTraceAgreement
    unfold ReadEventReplayAgreement at h_read
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_state_replay event.ptr.toNat]
      exact h_read.1
    · rw [h_state_replay (event.ptr.toNat + 1)]
      exact h_read.2.1
    · rw [h_state_replay (event.ptr.toNat + 2)]
      exact h_read.2.2.1
    · rw [h_state_replay (event.ptr.toNat + 3)]
      exact h_read.2.2.2.1
    · rw [h_state_replay (event.ptr.toNat + 4)]
      exact h_read.2.2.2.2.1
    · rw [h_state_replay (event.ptr.toNat + 5)]
      exact h_read.2.2.2.2.2.1
    · rw [h_state_replay (event.ptr.toNat + 6)]
      exact h_read.2.2.2.2.2.2.1
    · rw [h_state_replay (event.ptr.toNat + 7)]
      exact h_read.2.2.2.2.2.2.2

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
