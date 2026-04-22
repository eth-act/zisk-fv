import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.StoreD
import ZiskFv.Spec.StoreB
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.sb
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.StoreArchetype

/-!
End-to-end theorem for RV64 SB (store byte) — Phase 3A S2. Mirrors
`Equivalence.StoreH` / `Equivalence.StoreW` narrowed to a 1-byte
store. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_SB`),
* the compositional SB spec (`ZiskFv.Spec.StoreB.store_b_compositional`),
  which in turn routes through the store archetype macro
  `store_archetype_copyb_c_packed`,
* the Sail pure-function equivalence
  (`PureSpec.execute_STOREB_pure_equiv`; closed via the trusted
  memory-model axiom `execute_STOREB_pure_equiv_axiom` — see
  `RV64D/sb.lean` and `docs/fv/trusted-base.md` entry M11),

into three companion theorems paralleling the SH archetype:

* `equiv_SB` — circuit-level. States that the Main row's packed `c`
  lanes equal the **low 8 bits** of the 1-byte memory-bus write entry
  (the high 7 byte lanes are witnessed zero by the caller).
* `equiv_SB_sail` — Sail-level. Wraps `execute_STOREB_pure_equiv`.
* `equiv_SB_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.STORE …, 1) = (bus_effect …).2`.

As with `equiv_SH_metaplan`, the bus-emission correctness hypothesis
`h_bus_execute_matches_sail` is parameterized here (D3e DEFERRED shape
(e) — same parameterization verbatim as SD/SW/SH).
-/

namespace ZiskFv.Equivalence.StoreB

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreD
open ZiskFv.Spec.StoreB
open ZiskFv.Tactics.StoreArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SB theorem.** Given the store-archetype circuit
    constraints (identical to SD/SW/SH's — all use `OP_COPYB = 1`,
    `is_external_op = 0`, the same constraint subset, and the same
    `memory_store_lanes_match` predicate on the `c` lanes) plus the
    SB-specific high-byte-zeroing witness on the memory-bus write
    entry, the Main row's packed `c` cell equals the low 8 bits of
    the 1-byte memory-bus write entry.

    Routes through `store_archetype_copyb_c_packed` (the store
    archetype macro), then specializes via
    `memory_entry_toField_of_high_zero_8` to the low-8 form. -/
theorem equiv_SB
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_zero : sb_high_bytes_zero entry) :
    main_c_packed m r_main = memory_entry_lo_8 entry :=
  store_b_compositional m r_main next_pc entry h_circuit h_zero

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SB (`.STORE (imm, rs2, rs1, 1)`) reduces to the pure-function
    block supplied by `PureSpec.execute_STOREB_pure`, given the
    register/PC assumptions (SB has no alignment requirement).

    Wraps `PureSpec.execute_STOREB_pure_equiv`, which delegates to the
    trusted `execute_STOREB_pure_equiv_axiom` (Phase 3A S2; see
    `RV64D/sb.lean` and `docs/fv/trusted-base.md` entry M11). -/
theorem equiv_SB_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sb_state_assumptions sb_input state) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state
      = let output := PureSpec.execute_STOREB_pure sb_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_1 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STOREB_pure_equiv
    sb_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 SB:
    Sail's `execute_instruction` on an SB equals the state computed
    by applying `bus_effect` to the circuit's execution + memory bus
    rows.

    Composes `equiv_SB_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_SH_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4
    (or a future D3 shape-(e) closure) derives it from PIL-level bus
    emission. Note the width literal `1` in the `instruction.STORE`
    payload — the only surface-level difference from `equiv_SH_metaplan`.

    **Hypotheses.**
    * Sail side (from `equiv_SB_sail`): full `RISC_V_assumptions` +
      per-input `sb_state_assumptions` (register readability rs1/rs2,
      PC, address-space bound — no alignment for a 1-byte store).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution bus (read PC, write nextPC) + memory bus
      (register-read rs1, register-read rs2, **memory-write 1 byte**
      at `rs1 + imm`) fed through `bus_effect` produces the same
      `EStateM.Result` as the concrete Sail monadic block in
      `equiv_SB_sail`'s conclusion. -/
theorem equiv_SB_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sb_state_assumptions sb_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_STOREB_pure sb_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             set (PureSpec.modify_memory_1 (← get) output)
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_SB_sail state sb_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.StoreB
