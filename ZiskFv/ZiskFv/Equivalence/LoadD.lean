import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadD
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.ld
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LD (load doubleword). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LD`),
* the compositional LD spec
  (`ZiskFv.Spec.LoadD.load_d_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LOADD_pure_equiv`; closed via the trusted
  memory-model axiom `execute_LOADD_pure_equiv_axiom` — see
  `RV64D/ld.lean` and `docs/fv/trusted-base.md` entry M1),

into three companion theorems paralleling the ADD and BEQ archetypes:

* `equiv_LD` — circuit-level. States that the Main row's packed `c`
  lanes (as FGL) equal the 8-byte memory-bus entry's packed value,
  given the constraint-set + mode + memory-match hypotheses.
* `equiv_LD_sail` — Sail-level. Wraps `execute_LOADD_pure_equiv`.
* `equiv_LD_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.LOAD …) = (bus_effect …).2`.

As with the ADD/BEQ archetypes, the bus-emission correctness
hypothesis `h_bus_execute_matches_sail` is parameterized — Phase 4
audit derives it from a PIL-level bus-emission spec.
-/

namespace ZiskFv.Equivalence.LoadD

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LD theorem.** Given the load-subset Main
    constraints plus the mode witnesses from `transpile_LD` plus the
    memory-bus matching hypothesis, the Main row's packed `c` cell
    encodes the 8-byte loaded value packed from the memory-bus entry's
    byte lanes.

    This is the LD-analogue of `equiv_ADD` (for ADD) and
    `equiv_BEQ` (for BEQ): a single field equation at the circuit
    level, parameterized on the trace the caller supplies. -/
theorem equiv_LD
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : load_d_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry :=
  load_d_compositional m r_main next_pc entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LD (`.LOAD (imm, rs1, rd, false, 8)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADD_pure`,
    given the register/PC/memory/alignment assumptions.

    Wraps `PureSpec.execute_LOADD_pure_equiv`, which delegates to the
    trusted `execute_LOADD_pure_equiv_axiom` (Phase 2.5 D1; see
    `RV64D/ld.lean` and `docs/fv/trusted-base.md` M1). -/
theorem equiv_LD_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.ld_state_assumptions ld_input state) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state
      = let output := PureSpec.execute_LOADD_pure ld_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADD_pure_equiv
    ld_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 LD: Sail's
    `execute_instruction` on an LD equals the state computed by applying
    `bus_effect` to the circuit's execution + memory bus rows.

    Composes `equiv_LD_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_ADD_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4
    derives it from PIL-level bus emission.

    **Hypotheses.**
    * Sail side (from `equiv_LD_sail`): full `RISC_V_assumptions` +
      per-input `ld_state_assumptions` (register readability, PC,
      8 memory bytes, address-space bound, 8-byte alignment).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution bus (read PC, write nextPC) + memory bus
      (register-read rs1, memory-read 8 bytes, register-write rd)
      fed through `bus_effect` produces the same `EStateM.Result`
      as the concrete Sail monadic block in `equiv_LD_sail`'s
      conclusion. -/
theorem equiv_LD_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.ld_state_assumptions ld_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADD_pure ld_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             match output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LD_sail state ld_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.LoadD
