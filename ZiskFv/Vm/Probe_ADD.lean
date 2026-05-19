import ZiskFv.Compliance.Wrappers.Add
import ZiskFv.Vm.StateEffect

/-!
# Phase 2 probe — `equiv_ADD_v2` derived from `equiv_ADD`

This file is the Phase-2 architectural validation: prove
`equiv_ADD_v2` (channel-balance form) as a corollary of the existing
`equiv_ADD` (bus_effect form). The conversion is one rewrite step
via `state_effect_via_channels_eq_bus_effect_2`.

If this compiles for ADD, the same Phase-4 wrapper pattern works
for all 63 opcodes: each `equiv_<OP>_v2` invokes the corresponding
`equiv_<OP>` then applies the bridge theorem. The v1 and v2 forms
coexist throughout Phases 3-5, and Phase 6 deletes the v1 layer.

## Trust note

No axiom added. `equiv_ADD_v2`'s axiom closure is exactly
`equiv_ADD`'s closure (the bridge theorem is `rfl`).
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main add_subset_holds)
open ZiskFv.Trusted (OP_ADD)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- `equiv_ADD_v2` — the channel-balance-shaped canonical theorem
    for ADD. Same hypotheses as `equiv_ADD`; conclusion uses
    `state_effect_via_channels` instead of `bus_effect.2`. -/
theorem equiv_ADD_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (badd : ZiskFv.Compliance.BinaryAddWitness C)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADD
    state add_input r1 r2 rd m badd r_main bus pins h_main_subset h_lane_rd promises

end ZiskFv.Vm.Probe
