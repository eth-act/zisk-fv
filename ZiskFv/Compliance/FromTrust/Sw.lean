import Mathlib

import ZiskFv.Equivalence.StoreW
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_SW` Compliance wrapper — Mem-stores shape, 4-byte width

> **Status:** wrapper.
> Mirrors `Compliance/FromTrust/Sb.lean` specialized to SW's 4-byte
> store. Consumes `main_store_emission_bundle_sw` (class #4, NEW) via
> `Bridge.Mem.sw_discharge_full` to discharge the bundled `h_mem_eq`
> hypothesis on the canonical `equiv_SW` theorem.

## Discharge

`equiv_SW` carries a single bundled `h_mem_eq` hypothesis equating
the bus side's 8-insert chain on `state.mem` with the Sail spec's
4-insert chain (via `modify_memory_4`). The high 4 byte lanes of
the store bus entry equal pre-existing memory contents (MemAlign RMW
protocol); re-inserting them is a no-op closed in pure Lean.

## Anti-laundering report

* **1 new axiom contributed.** `main_store_emission_bundle_sw`
  (class #4) — same family as SB/SH siblings and SD pilot.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Wrapper for `equiv_SW`.** Discharges `h_mem_eq` from the SW
    emission bundle + RMW high-byte preservation. -/
theorem equiv_SW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 4)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sw_state_assumptions sw_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREW_pure sw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_read_r1 := h_opcode_assumptions.2.1
  have h_read_r2 := h_opcode_assumptions.2.2.1
  have h_mem_eq :=
    ZiskFv.Equivalence.Bridge.Mem.sw_discharge_full
      main r_main e2 state sw_input
      h_main_active h_main_op h_main_ind_width
      h_m2_mult h_m2_as h_read_r1 h_read_r2
  exact ZiskFv.Equivalence.StoreW.equiv_SW
    state sw_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2
    { risc_v_assumptions := risc_v_assumptions
      opcode_assumptions_ := h_opcode_assumptions
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := h_m0_mult
      m0_as := h_m0_as
      m1_mult := h_m1_mult
      m1_as := h_m1_as
      m2_mult := h_m2_mult
      m2_as := h_m2_as }
    h_mem_eq

end ZiskFv.Compliance
