import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.StoreD
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.sd
import ZiskFv.SailSpec.BusEffect
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 SD (store doubleword). The
`equiv_SD` discharges via structural bus hypotheses
(`bus_effect_matches_sail_store_rrrw`) plus a ptr-match between the
bus's mem-write entry pointer and Sail's `r1_val + signExtend imm`,
plus per-byte byte-match between the bus entry's lanes and the
extracted bytes of `r2_val`. -/

namespace ZiskFv.EquivCore.Sd

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD


lemma equiv_SD_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sd_state_assumptions sd_input state) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state
      = let output := PureSpec.execute_STORED_pure sd_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_8 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STORED_pure_equiv
    sd_input risc_v_assumptions h_opcode_assumptions

/-- **Canonical equivalence.** Discharges via structural bus hypotheses
    plus ptr/byte match parameters that bridge the bus's mem-write
    entry to Sail's `modify_memory_8` shape. -/
theorem equiv_SD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_ptr_match :
      bus.e2.ptr.toNat
        = (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_byte_0 : ((byteAt bus.e2 0) : BitVec 8) = BitVec.extractLsb 7 0 sd_input.r2_val)
    (h_byte_1 : ((byteAt bus.e2 1) : BitVec 8) = BitVec.extractLsb 15 8 sd_input.r2_val)
    (h_byte_2 : ((byteAt bus.e2 2) : BitVec 8) = BitVec.extractLsb 23 16 sd_input.r2_val)
    (h_byte_3 : ((byteAt bus.e2 3) : BitVec 8) = BitVec.extractLsb 31 24 sd_input.r2_val)
    (h_byte_4 : ((byteAt bus.e2 4) : BitVec 8) = BitVec.extractLsb 39 32 sd_input.r2_val)
    (h_byte_5 : ((byteAt bus.e2 5) : BitVec 8) = BitVec.extractLsb 47 40 sd_input.r2_val)
    (h_byte_6 : ((byteAt bus.e2 6) : BitVec 8) = BitVec.extractLsb 55 48 sd_input.r2_val)
    (h_byte_7 : ((byteAt bus.e2 7) : BitVec 8) = BitVec.extractLsb 63 56 sd_input.r2_val) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as⟩ := promises
  rw [equiv_SD_sail state sd_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_store_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_STORED_pure sd_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  -- Both sides have the same `Sail.writeReg Register.nextPC` step;
  -- after that, the bus side has `modify (fun s => {s with mem := <8 inserts>})`
  -- and the Sail side has `set (modify_memory_8 (← get) output)`. We
  -- rewrite output's data fields to the bus entry's fields and show
  -- the resulting state-update functions are equal.
  simp only [PureSpec.execute_STORED_pure, PureSpec.modify_memory_8,
             h_ptr_match, h_byte_0, h_byte_1, h_byte_2, h_byte_3,
             h_byte_4, h_byte_5, h_byte_6, h_byte_7]
  -- After substitution, both sides agree as monadic actions over the
  -- post-writeReg state. Strip monad machinery.
  simp [bind, pure, EStateM.bind, EStateM.pure, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, set,
        MonadStateOf.set, EStateM.set, get, MonadState.get, getThe,
        MonadStateOf.get, EStateM.get,
        Sail.writeReg, PreSail.writeReg]

end ZiskFv.EquivCore.Sd
