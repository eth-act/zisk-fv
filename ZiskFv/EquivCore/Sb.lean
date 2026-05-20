import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.StoreD
import ZiskFv.ZiskCircuit.StoreB
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.sb
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.StoreArchetype
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 SB (store byte).
-/

namespace ZiskFv.EquivCore.Sb

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD
open ZiskFv.ZiskCircuit.StoreB
open ZiskFv.Tactics.StoreArchetype


lemma equiv_SB_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sb_state_assumptions sb_input state) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state
      = let output := PureSpec.execute_STOREB_pure sb_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_1 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STOREB_pure_equiv
    sb_input risc_v_assumptions h_opcode_assumptions

/-- **Canonical equivalence.** -/
theorem equiv_SB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_mem_eq :
      (((((((state.mem.insert bus.e2.ptr.toNat bus.e2.x0
          ).insert (bus.e2.ptr.toNat + 1) bus.e2.x1
          ).insert (bus.e2.ptr.toNat + 2) bus.e2.x2
          ).insert (bus.e2.ptr.toNat + 3) bus.e2.x3
          ).insert (bus.e2.ptr.toNat + 4) bus.e2.x4
          ).insert (bus.e2.ptr.toNat + 5) bus.e2.x5
          ).insert (bus.e2.ptr.toNat + 6) bus.e2.x6
          ).insert (bus.e2.ptr.toNat + 7) bus.e2.x7
        = state.mem.insert
            (PureSpec.execute_STOREB_pure sb_input).data0.1
            (PureSpec.execute_STOREB_pure sb_input).data0.2) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as⟩ := promises
  rw [equiv_SB_sail state sb_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_store_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp [bind, pure, EStateM.bind, EStateM.pure, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, set,
        MonadStateOf.set, EStateM.set, get, MonadState.get, getThe,
        MonadStateOf.get, EStateM.get,
        Sail.writeReg, PreSail.writeReg,
        PureSpec.modify_memory_1]
  exact h_mem_eq

end ZiskFv.EquivCore.Sb
