import Mathlib

import ZiskFv.Equivalence.StoreH
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_SH` Compliance wrapper — Mem-stores shape, 2-byte width

> **Status:** wrapper (Step 4.2.r3.IV — Mem-stores narrow width).
> Mirrors `Compliance/FromTrust/Sb.lean` specialized to SH's 2-byte
> store. Consumes `main_store_emission_bundle_sh` (class #4, NEW) via
> `Bridge.Mem.sh_discharge_full` to discharge the bundled `h_mem_eq`
> hypothesis on the canonical `equiv_SH` theorem.

## Discharge

`equiv_SH` carries a single bundled `h_mem_eq` hypothesis equating
the bus side's 8-insert chain on `state.mem` with the Sail spec's
2-insert chain (via `modify_memory_2`). The high 6 byte lanes of
the store bus entry equal pre-existing memory contents (MemAlign RMW
protocol); re-inserting them is a no-op closed in pure Lean.

## Anti-laundering report

* **1 new axiom contributed.** `main_store_emission_bundle_sh`
  (class #4) — same family as the SB/SW siblings and SD pilot.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SH`.** Discharges `h_mem_eq` from the SH
    emission bundle + RMW high-byte preservation. -/
theorem equiv_SH_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 2)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sh_state_assumptions sh_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREH_pure sh_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_read_r1 := h_opcode_assumptions.2.1
  have h_read_r2 := h_opcode_assumptions.2.2.1
  have h_mem_eq :=
    ZiskFv.Equivalence.Bridge.Mem.sh_discharge_full
      main r_main e2 state sh_input
      h_main_active h_main_op h_main_ind_width
      h_m2_mult h_m2_as h_read_r1 h_read_r2
  exact ZiskFv.Equivalence.StoreH.equiv_SH
    state sh_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2 risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_mem_eq

end ZiskFv.Compliance
