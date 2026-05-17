import Mathlib

import ZiskFv.Equivalence.StoreD
import ZiskFv.Equivalence.Promises.Store
import ZiskFv.Equivalence.Promises.StoreHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_SD` Compliance wrapper — Mem-stores shape, 8-byte width

The wrapper takes the structural `StorePromises` bundle along with the
upstream activation/opcode pins on Main, and internally calls
`sd_h_mem_eq_of_emission` (which transitively consumes
`main_store_emission_bundle_sd` and `transpile_SD`) to derive the 9
ptr/byte equalities that the canonical `equiv_SD` consumes.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SD`.** Derives the 9 ptr+byte equalities from
    `sd_h_mem_eq_of_emission` (which consumes
    `main_store_emission_bundle_sd` + `transpile_SD`) and delegates to
    canonical `equiv_SD`. -/
theorem equiv_SD_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    -- AIR validator + row index.
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins on Main.
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    -- Sail-side opcode assumptions.
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state mstatus pmaRegion misa mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        exec_row e0 e1 e2) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  have h_mem_facts :=
    ZiskFv.Equivalence.Promises.sd_h_mem_eq_of_emission
      main r_main e2 state sd_input
      h_main_active h_main_op
      promises.m2_mult promises.m2_as h_opcode_assumptions
  ZiskFv.Equivalence.StoreD.equiv_SD
    state sd_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2 promises
    h_mem_facts.1 h_mem_facts.2.1 h_mem_facts.2.2.1 h_mem_facts.2.2.2.1
    h_mem_facts.2.2.2.2.1 h_mem_facts.2.2.2.2.2.1
    h_mem_facts.2.2.2.2.2.2.1 h_mem_facts.2.2.2.2.2.2.2.1
    h_mem_facts.2.2.2.2.2.2.2.2

end ZiskFv.Compliance
