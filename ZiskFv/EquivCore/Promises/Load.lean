import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.ZiskCircuit.MemTrace

/-!
# Load promise bundles for zero-extended LOAD opcodes

Covers LBU, LHU, LWU, LD (the copyb-family loads). The structural bundle carries
the shared non-memory binders; the canonical bundle adds the byte-agreement field
needed by the canonical load theorems. Opcode-specific extras (MemAlign*
providers for the sub-doubleword loads, mode pins, width pins) stay inline.

This bundle is part of the shared promise-family design in
`ZiskFv/EquivCore/Promises/`.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted
open ZiskFv.Channels.MemoryBusBytes (byteAt)

/-- Sail memory byte agreement for the load-side memory-bus entry. -/
def LoadByteAgreement
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (e : Interaction.MemoryBusEntry FGL) : Prop :=
  state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)
    ∧ state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4)
    ∧ state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5)
    ∧ state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6)
    ∧ state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7)

/-- Byte-agreement projection from the memory branch's stronger replay
agreement. -/
theorem loadByteAgreement_of_mem_trace_agreement
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (e : Interaction.MemoryBusEntry FGL)
    (h_agree :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e)) :
    LoadByteAgreement state e := by
  simpa [LoadByteAgreement] using
    ZiskFv.ZiskCircuit.MemTrace.byte_facts_of_event_agreement state e h_agree

/-- The current byte-agreement promise is definitionally the selected
`MemoryTraceAgreement` shape for `eventOfEntry`; this adapter keeps existing
callers compiling while the promise field is replaced by timeline evidence. -/
theorem memoryTraceAgreement_of_loadByteAgreement
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (e : Interaction.MemoryBusEntry FGL)
    (h_read : LoadByteAgreement state e) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e) := by
  simpa [LoadByteAgreement, ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement]
    using h_read

/-- Byte-agreement projection from the named residual timeline evidence. -/
theorem loadByteAgreement_of_memory_timeline_evidence
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (e : Interaction.MemoryBusEntry FGL)
    (evidence : ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state e) :
    LoadByteAgreement state e :=
  loadByteAgreement_of_mem_trace_agreement
    state e evidence.memoryTraceAgreement

/-- Structural load bundle for dispatch/envelope construction, excluding the
load-byte agreement that dispatch derives from the global memory timeline. -/
structure LoadStructuralPromises
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
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 1

/-- Canonical load promise bundle for LBU, LHU, LWU, LD. The memory byte
agreement remains here for canonical theorem calls; dispatch reconstructs this
field from `MemoryTimelineEvidence`. -/
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
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 1
  mem_read : LoadByteAgreement state e1

/-- Derive the canonical load promise shape from structural dispatch promises
and the named residual timeline evidence. -/
def LoadStructuralPromises.withMemoryTimelineEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (promises :
      LoadStructuralPromises state mstatus pmaRegion misa mseccfg opcode_assumptions
        pure_nextPC exec_row e0 e1 e2)
    (evidence : ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state e1) :
    LoadPromises state mstatus pmaRegion misa mseccfg opcode_assumptions pure_nextPC
      exec_row e0 e1 e2 :=
  { risc_v_assumptions := promises.risc_v_assumptions
    opcode_assumptions_ := promises.opcode_assumptions_
    exec_len := promises.exec_len
    e0_mult := promises.e0_mult
    e1_mult := promises.e1_mult
    nextPC_matches := promises.nextPC_matches
    m0_mult := promises.m0_mult
    m0_as := promises.m0_as
    m1_mult := promises.m1_mult
    m1_as := promises.m1_as
    m2_mult := promises.m2_mult
    m2_as := promises.m2_as
    mem_read := loadByteAgreement_of_memory_timeline_evidence state e1 evidence }

/-- Replace the legacy per-load byte agreement with the value derived from the
timeline evidence. This lets the global dispatcher ignore the constructor-carried
`mem_read` field while the `LoadPromises` shape is still being migrated. -/
def LoadPromises.withMemoryTimelineEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (promises :
      LoadPromises state mstatus pmaRegion misa mseccfg opcode_assumptions pure_nextPC
        exec_row e0 e1 e2)
    (evidence : ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state e1) :
    LoadPromises state mstatus pmaRegion misa mseccfg opcode_assumptions pure_nextPC
      exec_row e0 e1 e2 :=
  { promises with
    mem_read := loadByteAgreement_of_memory_timeline_evidence state e1 evidence }

end ZiskFv.EquivCore.Promises
