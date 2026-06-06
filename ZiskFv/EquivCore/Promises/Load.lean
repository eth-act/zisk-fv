import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.ZiskCircuit.MemTrace

/-!
# `LoadPromises` — structural bundle for zero-extended LOAD opcodes

Covers LBU, LHU, LWU, LD (the copyb-family loads). 12 structurally-
uniform binders shared by all four. Opcode-specific extras
(MemAlign* providers for the sub-doubleword loads, mode pins,
width pins) stay inline.

This bundle is part of the shared promise-family design in
`ZiskFv/EquivCore/Promises/`.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- 12-field structural bundle for LBU, LHU, LWU, LD. -/
structure LoadPromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (opcode_assumptions : Prop)
    (pure_nextPC : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg
  opcode_assumptions_ : opcode_assumptions
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC
  m0_mult : e0.multiplicity = -1
  m0_as : e0.as.val = 1
  m1_mult : e1.multiplicity = -1
  m1_as : e1.as.val = 2
  mem_trace_context :
    ZiskFv.ZiskCircuit.MemTrace.LoadTraceContext state
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1)
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 1

/-- Public memory burden carried by a load promise.

This is the theorem-shaped form of the replay obligation hidden inside the
load promise: the selected event must sit in an accepted trace, that accepted
trace must be replay-sound, the selected event must be a read, and the Sail
state must agree with replay memory at the selected cursor. -/
def LoadPromises.memoryBurden
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (promises : LoadPromises state mstatus pmaRegion misa mseccfg
      opcode_assumptions pure_nextPC exec_row e0 e1 e2) : Prop :=
  let ctx := promises.mem_trace_context
  (ZiskFv.ZiskCircuit.MemTrace.TraceReplaySound
      ctx.accepted.initialMemory ctx.trace
    ∧ ctx.trace =
        ctx.priorEvents ++ ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1 :: ctx.laterEvents
    ∧ (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).op = (1 : FGL)
    ∧ ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement state
        (ZiskFv.ZiskCircuit.MemTrace.replayEvents
          ctx.accepted.initialMemory ctx.priorEvents))

/-- Derived load memory agreement, consuming the public memory burden.

Keeping this as the only active projection prevents load proofs from silently
using constructor-carried trace evidence without the top-level burden premise
that exposes that evidence. -/
def LoadPromises.mem_trace_agreement
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (promises : LoadPromises state mstatus pmaRegion misa mseccfg
      opcode_assumptions pure_nextPC exec_row e0 e1 e2) :
    promises.memoryBurden →
    ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1) := by
  intro h_burden
  let ctx := promises.mem_trace_context
  dsimp [LoadPromises.memoryBurden] at h_burden
  rcases h_burden with
    ⟨h_trace_sound, h_trace_split, h_read, h_state_replay⟩
  have h_read_replay :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_trace_sound
      ctx.accepted.initialMemory ctx.priorEvents
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1) ctx.laterEvents
      (by simpa [h_trace_split] using h_trace_sound)
      h_read
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement
  unfold ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement at h_read_replay
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state_replay (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat]
    exact h_read_replay.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 1)]
    exact h_read_replay.2.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 2)]
    exact h_read_replay.2.2.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 3)]
    exact h_read_replay.2.2.2.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 4)]
    exact h_read_replay.2.2.2.2.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 5)]
    exact h_read_replay.2.2.2.2.2.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 6)]
    exact h_read_replay.2.2.2.2.2.2.1
  · rw [h_state_replay ((ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e1).ptr.toNat + 7)]
    exact h_read_replay.2.2.2.2.2.2.2

end ZiskFv.EquivCore.Promises
