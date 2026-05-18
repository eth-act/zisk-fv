import Mathlib

import ZiskFv.Equivalence.Sw
import ZiskFv.Equivalence.Promises.Store
import ZiskFv.Equivalence.Promises.StoreHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SW` Compliance wrapper — Mem-stores shape, 4-byte width

The wrapper takes the structural `StorePromises` bundle along with the
upstream activation/opcode/width pins on Main, and internally calls
`sw_h_mem_eq_of_emission` (which transitively consumes
`main_store_emission_bundle_sw` and `transpile_SW`) to derive the
`h_mem_eq` premise that the canonical `equiv_SW` consumes.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SW`.** Derives `h_mem_eq` from
    `sw_h_mem_eq_of_emission` (which consumes
    `main_store_emission_bundle_sw` + `transpile_SW`) and delegates to
    canonical `equiv_SW`. -/
theorem equiv_SW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validator + row index.
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins on Main.
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Width pin stays inline.
    (h_main_ind_width : main.ind_width r_main = 4)
    -- Sail-side opcode assumptions.
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  have h_mem_eq :=
    ZiskFv.Equivalence.Promises.sw_h_mem_eq_of_emission
      main r_main bus.e2 state sw_input
      pins.main_active pins.main_op h_main_ind_width
      promises.m2_mult promises.m2_as h_opcode_assumptions
  ZiskFv.Equivalence.Sw.equiv_SW
    state sw_input regs bus promises h_mem_eq

end ZiskFv.Compliance
