import ZiskFv.Compliance.Wrappers.Jalr
import ZiskFv.Channels.StateEffect

/-!
# `equiv_JALR` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for JALR. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_JALR`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Jalr.lean`.

## Trust note

The canonical route consumes Aeneas provenance for the selected final JALR
row, so mode pins do not come from `Trusted.transpile_JALR`.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main flag_boolean is_external_op_boolean flag_set_pc_disjoint
  pc_handshake_with_next_pc)
open ZiskFv.Trusted (OP_AND)

namespace ZiskFv.Equivalence.Jalr


theorem equiv_JALR
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
      flag_boolean m r_main
      ∧ is_external_op_boolean m r_main
      ∧ flag_set_pc_disjoint m r_main
      ∧ pc_handshake_with_next_pc m r_main next_pc)
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
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296)
    : (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_JALR_of_aeneas_provenance state jalr_input imm rs1 rd
    misa_val mseccfg exec_row e_rd nextPC_val m r_main next_pc store_pc_mem
    provenance h_jalr_subset promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
    h_link_bridge h_pc_bound h_pc_offset_lt_2_32

end ZiskFv.Equivalence.Jalr
