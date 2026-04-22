import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.StoreD
import ZiskFv.Spec.StoreH
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.sh
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.StoreArchetype

/-!
End-to-end theorem for RV64 SH (store halfword) — Phase 3A S1. Mirrors
`Equivalence.StoreW` narrowed from 4-byte to 2-byte store. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_SH`),
* the compositional SH spec (`ZiskFv.Spec.StoreH.store_h_compositional`),
  which in turn routes through the store archetype macro
  `store_archetype_copyb_c_packed`,
* the Sail pure-function equivalence
  (`PureSpec.execute_STOREH_pure_equiv`; closed via the trusted
  memory-model axiom `execute_STOREH_pure_equiv_axiom` — see
  `RV64D/sh.lean` and `docs/fv/trusted-base.md` entry M10),

into three companion theorems paralleling the SW archetype:

* `equiv_SH` — circuit-level. States that the Main row's packed `c`
  lanes equal the **low 16 bits** of the 2-byte memory-bus write entry
  (the high 6 byte lanes are witnessed zero by the caller).
* `equiv_SH_sail` — Sail-level. Wraps `execute_STOREH_pure_equiv`.
* `equiv_SH_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.STORE …, 2) = (bus_effect …).2`.

As with `equiv_SW_metaplan`, the bus-emission correctness hypothesis
`h_bus_execute_matches_sail` is parameterized here (D3e DEFERRED shape
(e) — same parameterization verbatim as SD/SW).
-/

namespace ZiskFv.Equivalence.StoreH

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreD
open ZiskFv.Spec.StoreH
open ZiskFv.Tactics.StoreArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SH theorem.** Given the store-archetype circuit
    constraints (identical to SD/SW's — all use `OP_COPYB = 1`,
    `is_external_op = 0`, the same constraint subset, and the same
    `memory_store_lanes_match` predicate on the `c` lanes) plus the
    SH-specific high-byte-zeroing witness on the memory-bus write
    entry, the Main row's packed `c` cell equals the low 16 bits of
    the 2-byte memory-bus write entry.

    Routes through `store_archetype_copyb_c_packed` (the store
    archetype macro), then specializes via
    `memory_entry_toField_of_high_zero_16` to the low-16 form. -/
theorem equiv_SH
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_zero : sh_high_bytes_zero entry) :
    main_c_packed m r_main = memory_entry_lo_16 entry :=
  store_h_compositional m r_main next_pc entry h_circuit h_zero

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SH (`.STORE (imm, rs2, rs1, 2)`) reduces to the pure-function
    block supplied by `PureSpec.execute_STOREH_pure`, given the
    register/PC/alignment assumptions.

    Wraps `PureSpec.execute_STOREH_pure_equiv`, which delegates to the
    trusted `execute_STOREH_pure_equiv_axiom` (Phase 3A S1; see
    `RV64D/sh.lean` and `docs/fv/trusted-base.md` entry M10). -/
theorem equiv_SH_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sh_state_assumptions sh_input state) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state
      = let output := PureSpec.execute_STOREH_pure sh_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_2 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STOREH_pure_equiv
    sh_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 SH:
    Sail's `execute_instruction` on an SH equals the state computed
    by applying `bus_effect` to the circuit's execution + memory bus
    rows.

    Composes `equiv_SH_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_SW_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4
    (or a future D3 shape-(e) closure) derives it from PIL-level bus
    emission. Note the width literal `2` in the `instruction.STORE`
    payload — the only surface-level difference from `equiv_SW_metaplan`.

    **Hypotheses.**
    * Sail side (from `equiv_SH_sail`): full `RISC_V_assumptions` +
      per-input `sh_state_assumptions` (register readability rs1/rs2,
      PC, address-space bound, 2-byte alignment).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution bus (read PC, write nextPC) + memory bus
      (register-read rs1, register-read rs2, **memory-write 2 bytes**
      at `rs1 + imm`) fed through `bus_effect` produces the same
      `EStateM.Result` as the concrete Sail monadic block in
      `equiv_SH_sail`'s conclusion. -/
theorem equiv_SH_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sh_state_assumptions sh_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_STOREH_pure sh_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             set (PureSpec.modify_memory_2 (← get) output)
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_SH_sail state sh_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.StoreH
