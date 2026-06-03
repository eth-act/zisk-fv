import ZiskFv.Compliance.Wrappers.Jal
import ZiskFv.Channels.StateEffect

/-!
# `equiv_JAL` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for JAL. The theorem is
route-parametric because production JAL has two bus shapes:
`rd != x0` uses one rd-write memory row, while `rd = x0` uses an empty
memory bus.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Jal.lean`.

## Trust note

The `rdWrite` route carries static-row provenance for the selected JAL row, so
mode pins are derived from the Aeneas lowering shape. The
`x0NoMemory` route delegates to the empty-memory JAL wrapper.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main jump_subset_holds)
open ZiskFv.Trusted (OP_FLAG)

namespace ZiskFv.Equivalence.Jal

/-- The two production JAL bus shapes. -/
inductive JalRoute
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main FGL FGL) (r_main : ℕ) where
  | rdWrite
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
      (nextPC_val : BitVec 64)
      (next_pc : FGL)
      (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
      {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
      (provenance : ZiskFv.Compliance.MainAeneasJalRowProvenance m r_main inst)
      (h_inst_rd_ne_zero : inst.rd ≠ 0#u32)
      (h_jal_subset : jump_subset_holds m r_main next_pc)
      (h_jmp2 : m.jmp_offset2 r_main = 4)
      (h_pc_bridge : (m.pc r_main).val = jal_input.PC.toNat)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < 18446744069414584321 - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296)
      : JalRoute state jal_input imm rd misa_val m r_main
  | x0NoMemory
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (nextPC_val : BitVec 64)
    (promises : ZiskFv.EquivCore.Promises.JumpNoMemPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
      : JalRoute state jal_input imm rd misa_val m r_main

namespace JalRoute

@[simp]
def channels
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {jal_input : PureSpec.JalInput}
    {imm : BitVec 21} {rd : regidx}
    {misa_val : RegisterType Register.misa}
    {m : Valid_Main FGL FGL} {r_main : ℕ}
    (route : JalRoute state jal_input imm rd misa_val m r_main) :
    ChannelEnsembleOutput :=
  match route with
  | .rdWrite exec_row e_rd .. => ⟨exec_row, [e_rd]⟩
  | .x0NoMemory exec_row _ _ _ _ => ⟨exec_row, []⟩

end JalRoute

theorem equiv_JAL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (route : JalRoute state jal_input imm rd misa_val m r_main)
    : execute_instruction (instruction.JAL (imm, rd)) state
      = state_effect_via_channels (JalRoute.channels route) state := by
  cases route with
  | rdWrite exec_row e_rd nextPC_val next_pc store_pc_mem provenance
      h_inst_rd_ne_zero h_jal_subset
      h_jmp2 h_pc_bridge
      promises h_input_imm h_not_throws h_pc_bound h_pc_offset_lt_2_32 =>
    change execute_instruction (instruction.JAL (imm, rd)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    exact ZiskFv.Compliance.equiv_JAL_of_aeneas_provenance
      state jal_input imm rd misa_val m r_main
      next_pc exec_row e_rd nextPC_val store_pc_mem
      provenance h_inst_rd_ne_zero h_jal_subset h_jmp2 h_pc_bridge
      promises h_input_imm h_not_throws h_pc_bound h_pc_offset_lt_2_32
  | x0NoMemory exec_row nextPC_val promises h_input_imm h_not_throws =>
    change execute_instruction (instruction.JAL (imm, rd)) state
      = state_effect_via_channels ⟨exec_row, []⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    exact ZiskFv.Compliance.equiv_JAL_x0_no_memory
      state jal_input imm rd misa_val exec_row nextPC_val
      promises h_input_imm h_not_throws

end ZiskFv.Equivalence.Jal
