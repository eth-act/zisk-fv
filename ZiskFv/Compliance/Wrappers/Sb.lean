import Mathlib

import ZiskFv.Equivalence_v1.Sb
import ZiskFv.Equivalence_v1.Promises.Store
import ZiskFv.Equivalence_v1.Promises.StoreHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SB` Compliance wrapper — Mem-stores shape, 1-byte width

The wrapper takes the structural `StorePromises` bundle along with the
upstream activation/opcode/width pins on Main, and internally calls
`sb_h_mem_eq_of_emission` (which transitively consumes
`main_store_emission_bundle_sb` and `transpile_SB`) to derive the
`h_mem_eq` premise that the canonical `equiv_SB` consumes. This keeps
both axioms transitively reachable from the global compliance theorem.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD
open ZiskFv.ZiskCircuit.StoreB


/-- **Wrapper for `equiv_SB`.** Derives `h_mem_eq` from
    `sb_h_mem_eq_of_emission` (which consumes
    `main_store_emission_bundle_sb` + `transpile_SB`) and delegates to
    canonical `equiv_SB`. -/
theorem equiv_SB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validator + row index. Compliance.lean shares `main`.
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins on Main (consumed by the StoreHelpers
    -- helper that transitively fires `transpile_SB` and
    -- `main_store_emission_bundle_sb`).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Width pin stays inline (per-opcode literal).
    (h_main_ind_width : main.ind_width r_main = 1)
    -- Sail-side opcode assumptions (also consumed by the helper).
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.Equivalence_v1.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  have h_mem_eq :=
    ZiskFv.Equivalence_v1.Promises.sb_h_mem_eq_of_emission
      main r_main bus.e2 state sb_input
      pins.main_active pins.main_op h_main_ind_width
      promises.m2_mult promises.m2_as h_opcode_assumptions
  ZiskFv.Equivalence_v1.Sb.equiv_SB
    state sb_input regs bus promises h_mem_eq

end ZiskFv.Compliance
