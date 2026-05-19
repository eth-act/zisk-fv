import ZiskFv.Compliance.Wrappers.Ld
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probe — LD `equiv_<OP>_v2` corollary (Load family representative)

One v2 wrapper for LD (64-bit doubleword load). The other 6 loads
(LW, LH, LB, LWU, LHU, LBU) follow the same one-line pattern with
sign-extension or zero-extension variants of the same Mem-paired
shape.

LD's parameter shape:
- Valid_Main + Valid_Mem + BusRows + ModeRegsFull
- LoadPromises (12-field structural promise)
- mem-bus has 3 entries: pc-fetch, address+timestamp, data-load

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_LD_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LD
    state ld_input regs main mem r_main bus pins promises

end ZiskFv.Vm.Probe
