import ZiskFv.Compliance.Wrappers.Fence
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probe — Fence `equiv_<OP>_v2` corollary

One v2 wrapper for FENCE (no memory effect; empty mem_rows list).

JAL and JALR are omitted: their wrappers take 4-8 additional FGL-
arithmetic / Sail-state hypotheses (h_input_imm, h_cur_privilege,
h_mseccfg, h_pc_bound, h_lo_bound, h_pc_offset_lt_2_32, ...). The
v2 form is mechanical but the parameter list is impractically long
for a probe — follow-up.

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Trusted (OP_FLAG)

namespace ZiskFv.Vm.Probe


theorem equiv_FENCE_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (_pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_FLAG)
    (promises : ZiskFv.Equivalence_v1.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = state_effect_via_channels ⟨exec_row, []⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_FENCE
    state fence_input fm pred succ rs rd main r_main exec_row _pins promises

end ZiskFv.Vm.Probe
