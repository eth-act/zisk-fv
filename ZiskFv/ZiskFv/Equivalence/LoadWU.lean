import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadWU
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.lwu
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LWU (load word, unsigned / zero-extended).
Phase 2.5 D4c sibling of `Equivalence/LoadD.lean`. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LWU`),
* the compositional LWU spec
  (`ZiskFv.Spec.LoadWU.load_wu_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LOADWU_pure_equiv`; closed via the trusted
  memory-model axiom `execute_LOADWU_pure_equiv_axiom` — see
  `RV64D/lwu.lean` — sibling of M1),

into three companion theorems paralleling LD's trio:

* `equiv_LWU` — circuit-level. States that the Main row's packed `c`
  lanes equal the 32-bit memory-bus entry's low half, given the
  constraint-set + mode + memory-match + high-bytes-zero hypotheses.
* `equiv_LWU_sail` — Sail-level. Wraps `execute_LOADWU_pure_equiv`.
* `equiv_LWU_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.LOAD (imm, rs1, rd, true, 4)) state
    = (bus_effect exec_row mem_row state).2`.

As with LD (`equiv_LD_metaplan`), the bus-emission correctness
hypothesis `h_bus_execute_matches_sail` is parameterized — LD's shape
(d) was DEFERRED per D3e (see Phase 2.5 Track D3 status). LWU inherits
the same parameterization until shape (d) closes.
-/

namespace ZiskFv.Equivalence.LoadWU

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD
open ZiskFv.Spec.LoadWU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LWU theorem.** With the LD-shape load hypotheses
    plus the memory-bus entry's high 4 byte lanes zeroed (the `ind_width
    = 4` bus-side zero-pad), the Main row's packed `c` cell encodes the
    32-bit loaded value (equal to `memory_entry_lo entry`).

    LWU-analogue of `equiv_LD`, narrowed via
    `load_wu_compositional`. -/
theorem equiv_LWU
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : load_wu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_lo entry :=
  load_wu_compositional m r_main next_pc entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LWU (`.LOAD (imm, rs1, rd, true, 4)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADWU_pure`,
    given the register/PC/memory/alignment assumptions.

    Wraps `PureSpec.execute_LOADWU_pure_equiv`, which delegates to the
    trusted `execute_LOADWU_pure_equiv_axiom` (sibling of M1; see
    `RV64D/lwu.lean`). -/
theorem equiv_LWU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lwu_state_assumptions lwu_input state) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state
      = let output := PureSpec.execute_LOADWU_pure lwu_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADWU_pure_equiv
    lwu_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 LWU: Sail's
    `execute_instruction` on an LWU equals the state computed by applying
    `bus_effect` to the circuit's execution + memory bus rows.

    Composes `equiv_LWU_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_LD_metaplan`, the
    bus-emission-correctness obligation is parameterized; D3e DEFERRED
    shape (d) (memory-bus-read) — LWU inherits the parameterization. -/
theorem equiv_LWU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lwu_state_assumptions lwu_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADWU_pure lwu_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             match output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LWU_sail state lwu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.LoadWU
