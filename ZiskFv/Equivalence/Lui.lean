import ZiskFv.Compliance.Wrappers.Lui
import ZiskFv.Channels.StateEffect

/-!
# `equiv_LUI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LUI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_LUI`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Lui.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_LUI`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Tactics.UTypeArchetype (lui_subset_holds auipc_subset_holds)
open ZiskFv.Trusted (OP_COPYB OP_FLAG)

namespace ZiskFv.Equivalence.Lui


theorem equiv_LUI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64))
    : execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LUI state lui_input imm rd m r_main next_pc exec_row e_rd
    store_pc_mem pins h_lui_subset promises

end ZiskFv.Equivalence.Lui
