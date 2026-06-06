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
    (mem : Std.HashMap Nat FGL) (addr : Nat) (byte : FGL) :
    Std.HashMap Nat FGL :=
  mem.insert addr byte

/-- Replay a store event into a byte-addressed memory map. The Mem AIR emits
8 lanes; narrow store callers use the event width to select the written
prefix. -/
def replayStoreEvent (mem : Std.HashMap Nat FGL) (event : MemEvent) :
    Std.HashMap Nat FGL :=
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
def replayEvents (init : Std.HashMap Nat FGL) : List MemEvent → Std.HashMap Nat FGL
  | [] => init
  | event :: rest =>
      let mem :=
        if event.op = (2 : FGL) then replayStoreEvent init event else init
      replayEvents mem rest

/-- Accepted Mem trace facts needed by load soundness. This is the explicit
nonlocal proof boundary: future Mem AIR work should derive these fields from
the full accepted trace, rather than supplying per-load byte facts. -/
structure AcceptedMemTrace
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (trace : List MemEvent) : Type where
  initialMemoryAgreement : Prop
  storeReplaySound : Prop
  eventOrderingSound : Prop
  segmentCarrySound : Prop
  dualEventsSound : Prop
  readAgreement :
    ∀ event, event ∈ trace → event.op = (1 : FGL) →
      MemoryTraceAgreement state event

/-- Selected load event plus the accepted trace facts from which its Sail
memory agreement is derived. -/
structure LoadTraceContext
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent) : Type where
  trace : List MemEvent
  accepted : AcceptedMemTrace state trace
  selected : event ∈ trace
  read : event.op = (1 : FGL)

/-- The local load byte agreement obtained from the accepted Mem trace
context. -/
theorem memoryTraceAgreement_of_load_context
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : MemEvent)
    (ctx : LoadTraceContext state event) :
    MemoryTraceAgreement state event :=
  ctx.accepted.readAgreement event ctx.selected ctx.read

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

@[simp]
lemma eventOfEntry_byteAt (e : MemoryBusEntry FGL) (i : ℕ) :
    (eventOfEntry e).byteAt i = byteAt e i := by
  unfold eventOfEntry MemEvent.byteAt byteAt
  simp

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
