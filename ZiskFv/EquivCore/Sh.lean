import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.StoreD
import ZiskFv.ZiskCircuit.StoreH
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.sh
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.StoreArchetype
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.Bridge.MemClean

/-!
End-to-end theorem for RV64 SH (store halfword). Mirrors SW.
-/

namespace ZiskFv.EquivCore.Sh

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD
open ZiskFv.ZiskCircuit.StoreH
open ZiskFv.Tactics.StoreArchetype


lemma equiv_SH_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sh_state_assumptions sh_input state) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state
      = let output := PureSpec.execute_STOREH_pure sh_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_2 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STOREH_pure_equiv
    sh_input risc_v_assumptions h_opcode_assumptions

/-- **Canonical equivalence.** -/
lemma equiv_SH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Bridging premise: bus 8-insert chain on state.mem equals Sail's
    -- 2-insert chain (via modify_memory_2 data fields).
    (h_mem_eq :
      (((((((state.mem.insert bus.e2.ptr.toNat (byteAt bus.e2 0)
          ).insert (bus.e2.ptr.toNat + 1) (byteAt bus.e2 1)
          ).insert (bus.e2.ptr.toNat + 2) (byteAt bus.e2 2)
          ).insert (bus.e2.ptr.toNat + 3) (byteAt bus.e2 3)
          ).insert (bus.e2.ptr.toNat + 4) (byteAt bus.e2 4)
          ).insert (bus.e2.ptr.toNat + 5) (byteAt bus.e2 5)
          ).insert (bus.e2.ptr.toNat + 6) (byteAt bus.e2 6)
          ).insert (bus.e2.ptr.toNat + 7) (byteAt bus.e2 7)
        = (state.mem.insert
              (PureSpec.execute_STOREH_pure sh_input).data0.1
              (PureSpec.execute_STOREH_pure sh_input).data0.2
            ).insert
              (PureSpec.execute_STOREH_pure sh_input).data1.1
              (PureSpec.execute_STOREH_pure sh_input).data1.2) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as⟩ := promises
  rw [equiv_SH_sail state sh_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_store_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp [bind, pure, EStateM.bind, EStateM.pure, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, set,
        MonadStateOf.set, EStateM.set, get, MonadState.get, getThe,
        MonadStateOf.get, EStateM.get,
        Sail.writeReg, PreSail.writeReg,
        PureSpec.modify_memory_2]
  exact h_mem_eq

/-- Clean-backed staging variant for SH.

The low two bytes and pointer come from the Clean Main c/store message;
the high-byte preservation parameters are the remaining MemAlign RMW
facts. -/
lemma equiv_SH_clean_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (rs1 rs2 : Fin 32)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2))
    (h_addr2 :
      mainRow.rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_ind_width : main.ind_width r_main = 2)
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok sh_input.r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok sh_input.r2_val state)
    (h_b0_value : main.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : main.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  have h_mem_eq :=
    ZiskFv.EquivCore.Bridge.MemClean.sh_discharge_full_clean_provider
      main r_main mainRow bus.e2 state rs1 rs2 sh_input
      h_main_row h_main_spec h_store_pc h_main_c_match h_addr2
      h_active h_op_main h_ind_width h_read_r1 h_read_r2
      h_b0_value h_b1_value
      h_m2 h_m3 h_m4 h_m5 h_m6 h_m7
  exact equiv_SH state sh_input regs bus promises h_mem_eq

lemma equiv_SH_clean_provider_witness
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 2)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    (w : ZiskFv.EquivCore.Bridge.MemClean.ShCleanWitness
        main r_main bus state sh_input) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  have h_read_r1 := h_opcode_assumptions.2.1
  have h_read_r2 := h_opcode_assumptions.2.2.1
  have h_read_r1' :
      read_xreg (regidx_to_fin (regidx.Regidx sh_input.r1)) state
        = EStateM.Result.ok sh_input.r1_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sh_input.r1)
          (regidx_to_fin (regidx.Regidx sh_input.r1))
          (by simp [regidx_to_fin])]
    exact h_read_r1
  have h_read_r2' :
      read_xreg (regidx_to_fin (regidx.Regidx sh_input.r2)) state
        = EStateM.Result.ok sh_input.r2_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sh_input.r2)
          (regidx_to_fin (regidx.Regidx sh_input.r2))
          (by simp [regidx_to_fin])]
    exact h_read_r2
  exact equiv_SH_clean_provider state sh_input regs bus promises
    main r_main w.mainRow
    (regidx_to_fin (regidx.Regidx sh_input.r1))
    (regidx_to_fin (regidx.Regidx sh_input.r2))
    w.main_row w.main_spec w.store_pc w.main_c_match w.addr2
    pins.main_active pins.main_op h_main_ind_width h_read_r1' h_read_r2'
    w.b0_value w.b1_value
    w.m2 w.m3 w.m4 w.m5 w.m6 w.m7

end ZiskFv.EquivCore.Sh
