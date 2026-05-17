import Mathlib

import ZiskFv.Equivalence.StoreH
import ZiskFv.Equivalence.Promises.Store
import ZiskFv.Equivalence.Promises.StoreHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_SH` Compliance wrapper — Mem-stores shape, 2-byte width

The wrapper takes the structural `StorePromises` bundle along with the
upstream activation/opcode/width pins on Main, and internally calls
`sh_h_mem_eq_of_emission` (which transitively consumes
`main_store_emission_bundle_sh` and `transpile_SH`) to derive the
`h_mem_eq` premise that the canonical `equiv_SH` consumes.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SH`.** Derives `h_mem_eq` from
    `sh_h_mem_eq_of_emission` (which consumes
    `main_store_emission_bundle_sh` + `transpile_SH`) and delegates to
    canonical `equiv_SH`. -/
theorem equiv_SH_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    -- AIR validator + row index.
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode / width pins on Main.
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 2)
    -- Sail-side opcode assumptions.
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state mstatus pmaRegion misa mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        exec_row e0 e1 e2) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  have h_mem_eq :=
    ZiskFv.Equivalence.Promises.sh_h_mem_eq_of_emission
      main r_main e2 state sh_input
      h_main_active h_main_op h_main_ind_width
      promises.m2_mult promises.m2_as h_opcode_assumptions
  ZiskFv.Equivalence.StoreH.equiv_SH
    state sh_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2 promises h_mem_eq

end ZiskFv.Compliance
