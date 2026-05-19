import ZiskFv.Vm.Probe_UTYPE

/-!
# `equiv_LUI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LUI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_LUI_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Lui.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_LUI_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Tactics.UTypeArchetype (lui_subset_holds auipc_subset_holds)
open ZiskFv.Trusted (OP_COPYB OP_FLAG)

namespace ZiskFv.Equivalence.Lui

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_LUI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence_v1.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64))
    : execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state :=
  ZiskFv.Vm.Probe.equiv_LUI_v2 state lui_input imm rd m r_main next_pc exec_row e_rd pins h_lui_subset promises

end ZiskFv.Equivalence.Lui
