import ZiskFv.Compliance.Wrappers.Sd
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probe — SD `equiv_<OP>_v2` corollary (Store family representative)

One v2 wrapper for SD (64-bit doubleword store). SW, SH, SB follow
the same Store-shape pattern with width variants.

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Vm.Probe


theorem equiv_SD_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    (promises : ZiskFv.Equivalence_v1.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SD
    state sd_input regs main r_main bus pins h_opcode_assumptions promises

end ZiskFv.Vm.Probe
