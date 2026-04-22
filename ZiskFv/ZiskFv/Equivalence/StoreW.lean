import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.StoreD
import ZiskFv.Spec.StoreW
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.sw
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.StoreArchetype

/-!
End-to-end theorem for RV64 SW (store word) — Phase 2.5 D4d. Mirrors
`Equivalence.StoreD` narrowed from 8-byte to 4-byte store. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_SW`),
* the compositional SW spec (`ZiskFv.Spec.StoreW.store_w_compositional`),
  which in turn routes through the store archetype macro
  `store_archetype_copyb_c_packed` — **this is the first sibling
  instantiation of the store archetype and therefore the Phase 2.5 D4d
  validation of `Tactics.StoreArchetype`**,
* the Sail pure-function equivalence
  (`PureSpec.execute_STOREW_pure_equiv`; closed via the trusted
  memory-model axiom `execute_STOREW_pure_equiv_axiom` — see
  `RV64D/sw.lean` and `docs/fv/trusted-base.md`),

into three companion theorems paralleling the SD archetype:

* `equiv_SW` — circuit-level. States that the Main row's packed `c`
  lanes equal the **low 32 bits** of the 4-byte memory-bus write entry
  (the high 4 byte lanes are witnessed zero by the caller).
* `equiv_SW_sail` — Sail-level. Wraps `execute_STOREW_pure_equiv`.
* `equiv_SW_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.STORE …, 4) = (bus_effect …).2`.

As with `equiv_SD_metaplan`, the bus-emission correctness hypothesis
`h_bus_execute_matches_sail` is parameterized here — Phase 4 (or a
future D3 shape-(e) lemma) derives it from a PIL-level bus-emission
spec. The Phase 2.5 D3 decision for shape (e) memory-write was
DEFER, so SW inherits SD's parameterization verbatim.
-/

namespace ZiskFv.Equivalence.StoreW

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreD
open ZiskFv.Spec.StoreW
open ZiskFv.Tactics.StoreArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SW theorem.** Given the store-archetype circuit
    constraints (identical to SD's — both use `OP_COPYB = 1`,
    `is_external_op = 0`, the same constraint subset, and the same
    `memory_store_lanes_match` predicate on the `c` lanes) plus the
    SW-specific high-byte-zeroing witness on the memory-bus write
    entry, the Main row's packed `c` cell equals the low 32 bits of
    the 4-byte memory-bus write entry.

    **This theorem is the first sibling instantiation of the store
    archetype macro.** Its proof routes through
    `store_archetype_copyb_c_packed` (validating that the macro's
    parametric form produces the desired conclusion), then specializes
    via `memory_entry_toField_of_high_zero` to the low-32 form. -/
theorem equiv_SW
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_zero : sw_high_bytes_zero entry) :
    main_c_packed m r_main = memory_entry_lo entry :=
  store_w_compositional m r_main next_pc entry h_circuit h_zero

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SW (`.STORE (imm, rs2, rs1, 4)`) reduces to the pure-function
    block supplied by `PureSpec.execute_STOREW_pure`, given the
    register/PC/alignment assumptions.

    Wraps `PureSpec.execute_STOREW_pure_equiv`, which delegates to the
    trusted `execute_STOREW_pure_equiv_axiom` (Phase 2.5 D4d; see
    `RV64D/sw.lean` and `docs/fv/trusted-base.md`). -/
theorem equiv_SW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sw_state_assumptions sw_input state) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state
      = let output := PureSpec.execute_STOREW_pure sw_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_4 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STOREW_pure_equiv
    sw_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 SW:
    Sail's `execute_instruction` on an SW equals the state computed
    by applying `bus_effect` to the circuit's execution + memory bus
    rows.

    Composes `equiv_SW_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_SD_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4
    (or a future D3 shape-(e) closure) derives it from PIL-level bus
    emission. Note the width literal `4` in the `instruction.STORE`
    payload — the only surface-level difference from `equiv_SD_metaplan`.

    **Hypotheses.**
    * Sail side (from `equiv_SW_sail`): full `RISC_V_assumptions` +
      per-input `sw_state_assumptions` (register readability rs1/rs2,
      PC, address-space bound, 4-byte alignment).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution bus (read PC, write nextPC) + memory bus
      (register-read rs1, register-read rs2, **memory-write 4 bytes**
      at `rs1 + imm`) fed through `bus_effect` produces the same
      `EStateM.Result` as the concrete Sail monadic block in
      `equiv_SW_sail`'s conclusion. -/
theorem equiv_SW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sw_state_assumptions sw_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_STOREW_pure sw_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             set (PureSpec.modify_memory_4 (← get) output)
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_SW_sail state sw_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.StoreW
