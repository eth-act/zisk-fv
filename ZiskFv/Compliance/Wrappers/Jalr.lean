import Mathlib

import ZiskFv.EquivCore.Jalr
import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.EquivCore.Promises.JumpHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.AeneasRowProvenance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_JALR` Compliance wrapper — ControlFlow non-branch

The compatibility wrapper takes the structural `JumpPromises` bundle along
with upstream activation/opcode/mode pins on Main and internally calls
`jalr_h_circuit_of_main_constraints`. The canonical route below uses
Aeneas provenance instead.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main


/-- **Compatibility wrapper for `equiv_JALR`.** Derives `h_circuit` from
    explicit Main-row pins and delegates to canonical `equiv_JALR`. -/
lemma equiv_JALR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    -- Activation / opcode pins on Main + per-row subset constraint.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_flag : m.flag r_main = 0)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 1)
    (h_store_pc : m.store_pc r_main = 1)
    (h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m r_main
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m r_main
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r_main
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r_main next_pc)
    -- Structural `JumpPromises` bundle.
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jalr_input.PC jalr_input.rd misa_val
        (PureSpec.execute_JALR_pure jalr_input).success
        (PureSpec.execute_JALR_pure jalr_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_link_bridge :
      (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.EquivCore.Promises.jalr_h_circuit_of_main_constraints
      m r_main next_pc pins.main_active pins.main_op
      h_flag h_m32 h_set_pc h_store_pc h_jalr_subset
  ZiskFv.EquivCore.Jalr.equiv_JALR
    state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
    h_circuit h_link_bridge h_pc_bound h_pc_offset_lt_2_32

/-- Aeneas-provenance wrapper for `equiv_JALR`. Mode pins for the final JALR
    row come from the selected Aeneas-lowered row; `flag = 0` follows from
    `set_pc = 1` and the existing disjointness constraint. -/
lemma equiv_JALR_of_aeneas_provenance
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance :
      Sigma fun inst : ZiskFv.Transpiler.Aeneas.Rv64imInst =>
        ZiskFv.Compliance.MainAeneasJalrRowProvenance m r_main inst)
    (h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m r_main
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m r_main
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r_main
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jalr_input.PC jalr_input.rd misa_val
        (PureSpec.execute_JALR_pure jalr_input).success
        (PureSpec.execute_JALR_pure jalr_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_link_bridge :
      (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.EquivCore.Promises.jalr_h_circuit_of_aeneas_provenance
      m r_main next_pc provenance.2 h_jalr_subset
  ZiskFv.EquivCore.Jalr.equiv_JALR
    state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
    h_circuit h_link_bridge h_pc_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
