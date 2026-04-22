import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadBU
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.lbu
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LBU (load byte, unsigned / zero-extended).
Phase 3A L5 sibling of `Equivalence/LoadWU.lean` / `Equivalence/LoadHU.lean`.
Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LBU`),
* the compositional LBU spec
  (`ZiskFv.Spec.LoadBU.load_bu_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LOADBU_pure_equiv`; closed via the trusted
  memory-model axiom `execute_LOADBU_pure_equiv_axiom` — see
  `RV64D/lbu.lean` — sibling of M1/M3/M7/M9),

into three companion theorems paralleling LWU/LHU's trio:

* `equiv_LBU` — circuit-level. States that the Main row's packed `c`
  lanes equal the memory-bus entry's byte, given the constraint-set +
  mode + memory-match + high-bytes-zero hypotheses.
* `equiv_LBU_sail` — Sail-level. Wraps `execute_LOADBU_pure_equiv`.
* `equiv_LBU_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.LOAD (imm, rs1, rd, true, 1)) state
    = (bus_effect exec_row mem_row state).2`.

As with LWU / LHU (`equiv_LWU_metaplan` / `equiv_LHU_metaplan`), the
bus-emission correctness hypothesis `h_bus_execute_matches_sail` is
parameterized — D3e DEFERRED shape (d) (memory-bus-read) inherits to
LBU.
-/

namespace ZiskFv.Equivalence.LoadBU

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD
open ZiskFv.Spec.LoadBU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LBU theorem.** With the LD-shape load hypotheses
    plus the memory-bus entry's 7 high byte lanes zeroed (the
    `ind_width = 1` bus-side zero-pad), the Main row's packed `c` cell
    encodes the 8-bit loaded value (equal to `memory_entry_byte entry`).

    LBU-analogue of `equiv_LWU` / `equiv_LHU`, narrowed via
    `load_bu_compositional`. -/
theorem equiv_LBU
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : load_bu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_byte entry :=
  load_bu_compositional m r_main next_pc entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LBU (`.LOAD (imm, rs1, rd, true, 1)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADBU_pure`,
    given the register/PC/memory assumptions (alignment is vacuous
    for 1-byte loads).

    Wraps `PureSpec.execute_LOADBU_pure_equiv`, which delegates to the
    trusted `execute_LOADBU_pure_equiv_axiom` (sibling of M1/M3/M7;
    see `RV64D/lbu.lean`). -/
theorem equiv_LBU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lbu_state_assumptions lbu_input state) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state
      = let output := PureSpec.execute_LOADBU_pure lbu_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADBU_pure_equiv
    lbu_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 LBU: Sail's
    `execute_instruction` on an LBU equals the state computed by
    applying `bus_effect` to the circuit's execution + memory bus rows.

    Composes `equiv_LBU_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_LWU_metaplan` /
    `equiv_LHU_metaplan` / `equiv_LD_metaplan`, the
    bus-emission-correctness obligation is parameterized; D3e DEFERRED
    shape (d) (memory-bus-read) inherits here. -/
theorem equiv_LBU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lbu_state_assumptions lbu_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADBU_pure lbu_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             match output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LBU_sail state lbu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.LoadBU
