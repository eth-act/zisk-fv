import Mathlib

import ZiskFv.Equivalence.StoreB
import ZiskFv.Equivalence.Promises.Store
import ZiskFv.Equivalence.Promises.StoreHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

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

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SB`.** Derives `h_mem_eq` from
    `sb_h_mem_eq_of_emission` (which consumes
    `main_store_emission_bundle_sb` + `transpile_SB`) and delegates to
    canonical `equiv_SB`. -/
theorem equiv_SB_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    -- AIR validator + row index. Compliance.lean shares `main`.
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode / width pins on Main (consumed by the
    -- StoreHelpers helper that transitively fires `transpile_SB` and
    -- `main_store_emission_bundle_sb`).
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 1)
    -- Sail-side opcode assumptions (also consumed by the helper).
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state mstatus pmaRegion misa mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        exec_row e0 e1 e2) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  have h_mem_eq :=
    ZiskFv.Equivalence.Promises.sb_h_mem_eq_of_emission
      main r_main e2 state sb_input
      h_main_active h_main_op h_main_ind_width
      promises.m2_mult promises.m2_as h_opcode_assumptions
  ZiskFv.Equivalence.StoreB.equiv_SB
    state sb_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2 promises h_mem_eq

end ZiskFv.Compliance
