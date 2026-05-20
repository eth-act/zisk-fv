import ZiskFv.Compliance.Wrappers.Auipc
import ZiskFv.Vm.StateEffect

/-!
# `equiv_AUIPC` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for AUIPC. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_AUIPC`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Auipc.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_AUIPC`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Tactics.UTypeArchetype (lui_subset_holds auipc_subset_holds)
open ZiskFv.Trusted (OP_COPYB OP_FLAG)

namespace ZiskFv.Equivalence.Auipc


theorem equiv_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296)
    : execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_AUIPC state auipc_input imm rd exec_row e_rd nextPC_val m r_main next_pc pins h_auipc_subset promises h_no_wrap h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Equivalence.Auipc
