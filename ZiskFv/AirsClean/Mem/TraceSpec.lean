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

/-- Accepted full Mem trace facts for chronological raw memory-bus rows.

The rows are already projected to the public memory-bus row type used by the
load replay layer. `readWriteSound` is the semantic content needed for loads:
active memory reads emit the replayed value, and active memory writes update
the replay memory in bus-effect shape. The remaining fields name the global
AIR obligations that must eventually prove this object from accepted Mem trace
data rather than from caller evidence. -/
structure AcceptedFullMemoryBusRowsTrace
    (initialState : SailState)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type where
  initialMemory : Std.ExtHashMap Nat (BitVec 8)
  chronologicalRows : Prop
  sameAddressValuePreservation : Prop
  writeUpdateSound : Prop
  eventOrderingSound : Prop
  segmentCarrySound : Prop
  dualEventsSound : Prop
  readWriteSound : MemoryBusRowsReadWriteSound initialMemory rows
  initialAgreement : ReplayMemoryAgreement initialState initialMemory

/-- Lower the global Mem trace spec to the replay construction object consumed
    by the existing memory-load bridge. -/
def AcceptedFullMemoryBusRowsTrace.toRowsTraceConstruction
    {initialState : SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (trace : AcceptedFullMemoryBusRowsTrace initialState rows) :
    AcceptedMemoryBusRowsTraceConstruction initialState rows :=
  { initialMemory := trace.initialMemory
    storeReplaySound := trace.writeUpdateSound
    eventOrderingSound := trace.eventOrderingSound
    segmentCarrySound := trace.segmentCarrySound
    dualEventsSound := trace.dualEventsSound
    rowsReadWriteSound := trace.readWriteSound
    initialAgreement := trace.initialAgreement }

end ZiskFv.AirsClean.Mem
