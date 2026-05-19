import ZiskFv.Compliance.Wrappers.Jal
import ZiskFv.Compliance.Wrappers.Jalr
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — JAL / JALR v2 corollaries

Two jump opcodes. JAL takes a structural JumpPromises bundle + 4
arithmetic-bound hypotheses; JALR takes 8+ hypotheses including
privilege checks and PC overflow bounds.

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main jump_subset_holds)
open ZiskFv.Tactics.JumpArchetype (jalr_subset_holds)
open ZiskFv.Trusted (OP_FLAG OP_COPYB)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_JAL_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_jal_subset : jump_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < 18446744069414584321 - 4)
    (h_lo_bound : ↑(m.pc r_main + 4) < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_JAL state jal_input imm rd misa_val m r_main next_pc
    exec_row e_rd nextPC_val pins h_jal_subset
    promises h_input_imm h_not_throws
    h_pc_bound h_lo_bound h_pc_offset_lt_2_32

theorem equiv_JALR_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_jalr_subset : jalr_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.JumpPromises
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
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_JALR state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd nextPC_val m r_main next_pc
    pins h_jalr_subset
    promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
    h_pc_bound h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Vm.Probe
