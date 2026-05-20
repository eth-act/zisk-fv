import ZiskFv.Vm.Probe_Jal

/-!
# `equiv_JALR` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for JALR. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_JALR_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Jalr.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_JALR_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main jump_subset_holds)
open ZiskFv.Tactics.JumpArchetype (jalr_subset_holds)
open ZiskFv.Trusted (OP_FLAG OP_COPYB)

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
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_jalr_subset : jalr_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence_v1.Promises.JumpPromises
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
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296)
    : (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state :=
  ZiskFv.Vm.Probe.equiv_JALR_v2 state jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val m r_main next_pc pins h_jalr_subset promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg h_pc_bound h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Equivalence.Jalr
