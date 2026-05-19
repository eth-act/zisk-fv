import ZiskFv.Compliance.Wrappers.Lui
import ZiskFv.Compliance.Wrappers.Auipc
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — UTYPE family `equiv_<OP>_v2` corollaries

Two v2 wrappers for LUI and AUIPC. UTYPE writes the destination
register (so the channel ensemble has a single memory row, `e_rd`)
but doesn't read or branch.

## Trust note

No axioms added. Pure corollaries.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Tactics.UTypeArchetype (lui_subset_holds auipc_subset_holds)
open ZiskFv.Trusted (OP_COPYB OP_FLAG)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_LUI_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LUI
    state lui_input imm rd m r_main next_pc exec_row e_rd pins h_lui_subset promises

theorem equiv_AUIPC_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_AUIPC
    state auipc_input imm rd exec_row e_rd nextPC_val m r_main next_pc
    pins h_auipc_subset promises h_no_wrap h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Vm.Probe
