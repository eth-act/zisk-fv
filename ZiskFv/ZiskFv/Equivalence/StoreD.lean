import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.StoreD
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.sd
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 SD (store doubleword). Write-side mirror
of `Equivalence.LoadD`. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_SD`),
* the compositional SD spec
  (`ZiskFv.Spec.StoreD.store_d_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_STORED_pure_equiv`; closed via the trusted
  memory-model axiom `execute_STORED_pure_equiv_axiom` — see
  `RV64D/sd.lean` and `docs/fv/trusted-base.md` entry M2),

into three companion theorems paralleling the LD archetype:

* `equiv_SD` — circuit-level. States that the Main row's packed `c`
  lanes (as FGL) equal the 8-byte memory-bus **write** entry's
  packed value, given the constraint-set + mode + memory-match
  hypotheses.
* `equiv_SD_sail` — Sail-level. Wraps `execute_STORED_pure_equiv`.
* `equiv_SD_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.STORE …) = (bus_effect …).2`.

Unlike LD, SD has no register-write side-effect — the `bus_effect`
memory-write branch (`BusEffect.lean:90-103`) inserts the 8 bytes
into `state.mem` and returns `Retire_Success`. No option-rd branching.

As with LD/ADD/BEQ/etc., the bus-emission correctness hypothesis
`h_bus_execute_matches_sail` is parameterized — Phase 4 audit derives
it from a PIL-level bus-emission spec.
-/

namespace ZiskFv.Equivalence.StoreD

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SD theorem.** Given the store-subset Main
    constraints plus the mode witnesses from `transpile_SD` plus the
    memory-bus **write** matching hypothesis, the Main row's packed
    `c` cell encodes the 8-byte store value packed from the memory-bus
    write entry's byte lanes.

    This is the SD-analogue of `equiv_LD` (same conclusion shape,
    same hypothesis-composition pattern — just with
    `memory_store_lanes_match` replacing `memory_load_lanes_match` in
    the `store_d_circuit_holds` packaging). -/
theorem equiv_SD
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_d_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry :=
  store_d_compositional m r_main next_pc entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SD (`.STORE (imm, rs2, rs1, 8)`) reduces to the pure-function
    block supplied by `PureSpec.execute_STORED_pure`, given the
    register/PC/alignment assumptions.

    Wraps `PureSpec.execute_STORED_pure_equiv`, which delegates to the
    trusted `execute_STORED_pure_equiv_axiom` (Phase 2.5 D1; see
    `RV64D/sd.lean` and `docs/fv/trusted-base.md` M2). -/
theorem equiv_SD_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sd_state_assumptions sd_input state) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state
      = let output := PureSpec.execute_STORED_pure sd_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_8 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STORED_pure_equiv
    sd_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 SD:
    Sail's `execute_instruction` on an SD equals the state computed
    by applying `bus_effect` to the circuit's execution + memory bus
    rows.

    Composes `equiv_SD_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_LD_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4
    derives it from PIL-level bus emission.

    **Hypotheses.**
    * Sail side (from `equiv_SD_sail`): full `RISC_V_assumptions` +
      per-input `sd_state_assumptions` (register readability rs1/rs2,
      PC, address-space bound, 8-byte alignment).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution bus (read PC, write nextPC) + memory bus
      (register-read rs1, register-read rs2, **memory-write** 8 bytes
      at `rs1 + imm`) fed through `bus_effect` produces the same
      `EStateM.Result` as the concrete Sail monadic block in
      `equiv_SD_sail`'s conclusion. The `bus_effect` memory-write
      branch (`BusEffect.lean:90-103`) inserts 8 bytes and returns
      `Retire_Success`. -/
theorem equiv_SD_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sd_state_assumptions sd_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_STORED_pure sd_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             set (PureSpec.modify_memory_8 (← get) output)
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_SD_sail state sd_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.StoreD
