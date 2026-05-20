import ZiskFv.Compliance.Wrappers.Jal
import ZiskFv.Vm.StateEffect

/-!
# `equiv_JAL` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for JAL. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_JAL`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Jal.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_JAL`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main jump_subset_holds)
open ZiskFv.Tactics.JumpArchetype (jalr_subset_holds)
open ZiskFv.Trusted (OP_FLAG OP_COPYB)

namespace ZiskFv.Equivalence.Jal


theorem equiv_JAL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_jal_subset : jump_subset_holds m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < 18446744069414584321 - 4)
    (h_lo_bound : ↑(m.pc r_main + 4) < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296)
    : execute_instruction (instruction.JAL (imm, rd)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_JAL state jal_input imm rd misa_val m r_main next_pc exec_row e_rd nextPC_val pins h_jal_subset promises h_input_imm h_not_throws h_pc_bound h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Equivalence.Jal
