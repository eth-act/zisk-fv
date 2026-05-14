import Mathlib

import ZiskFv.Equivalence.StoreB
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_SB` Compliance wrapper — Mem-stores shape, 1-byte width

> **Status:** wrapper (Step 4.2.r3.IV — Mem-stores narrow width).
> Mirrors `Compliance/SdExemplar.lean` (SD pilot, commit `3a86908`)
> specialized to SB's 1-byte store. Consumes
> `main_store_emission_bundle_sb` (class #4, NEW) via
> `Bridge.Mem.sb_discharge_full` to discharge the bundled
> `h_mem_eq` hypothesis on the canonical `equiv_SB` theorem.

## Discharge

`equiv_SB` carries a single bundled `h_mem_eq` hypothesis equating
the bus side's 8-insert chain on `state.mem` with the Sail spec's
1-insert chain (via `modify_memory_1`). The RMW protocol of the
MemAlign* providers ensures the high 7 byte lanes of the store bus
entry equal the pre-existing memory contents at those addresses, so
re-inserting them is a no-op (`Std.ExtHashMap.ext_getElem?` closure
in `Bridge.Mem.sb_discharge_full`).

## Anti-laundering report

* **1 new axiom contributed to this wrapper.**
  `main_store_emission_bundle_sb` (`MemBridge.lean`, class #4).
  PIL-cited; same class as `main_store_emission_bundle_sd` —
  narrow-width variant with RMW high-byte preservation.
* **Caller-burden shrinks.** `h_mem_eq` (1 hypothesis encoding ptr +
  low byte + 7 high-byte RMW preservations) is discharged; replaced
  by `(main : Valid_Main, r_main, h_main_active, h_main_op,
  h_ind_width)` (5 lighter parameters).
-/

namespace ZiskFv.Equivalence.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.StoreD
open ZiskFv.Circuit.StoreB

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SB`.** Discharges `h_mem_eq` from the SB
    emission bundle + RMW high-byte preservation. -/
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
    -- Activation / opcode / width pins. Compliance.lean derives these
    -- from Main's ROM handshake on the row hosting SB.
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 1)
    -- Sail-side state predicates (SPEC-PRE).
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sb_state_assumptions sb_input state)
    -- Bus-protocol structural hypotheses — pass-through from `equiv_SB`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREB_pure sb_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Extract the rX_bits reads from sb_state_assumptions.
  have h_read_r1 := h_opcode_assumptions.2.1
  have h_read_r2 := h_opcode_assumptions.2.2.1
  -- Discharge h_mem_eq via the Mem-stores bridge.
  have h_mem_eq :=
    ZiskFv.Equivalence.Bridge.Mem.sb_discharge_full
      main r_main e2 state sb_input
      h_main_active h_main_op h_main_ind_width
      h_m2_mult h_m2_as h_read_r1 h_read_r2
  -- Delegate to canonical `equiv_SB`.
  exact ZiskFv.Equivalence.StoreB.equiv_SB
    state sb_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2 risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_mem_eq

end ZiskFv.Equivalence.Compliance
