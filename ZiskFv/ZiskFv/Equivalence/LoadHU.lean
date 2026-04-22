import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadHU
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.RV64D.lhu
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LHU (load halfword, unsigned / zero-extended).
Phase 3A L3 sibling of `Equivalence/LoadWU.lean`. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LHU`),
* the compositional LHU spec
  (`ZiskFv.Spec.LoadHU.load_hu_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LOADHU_pure_equiv`; closed via the trusted
  memory-model axiom `execute_LOADHU_pure_equiv_axiom` — see
  `RV64D/lhu.lean` — sibling of M1/M3/M5/M7),

into three companion theorems paralleling LWU's trio:

* `equiv_LHU` — circuit-level. States that the Main row's packed `c`
  lanes equal the memory-bus entry's 16-bit half, given the
  constraint-set + mode + memory-match + high-bytes-zero hypotheses.
* `equiv_LHU_sail` — Sail-level. Wraps `execute_LOADHU_pure_equiv`.
* `equiv_LHU_metaplan` — the metaplan-shaped theorem
  `execute_instruction (.LOAD (imm, rs1, rd, true, 2)) state
    = (bus_effect exec_row mem_row state).2`.

As with LWU (`equiv_LWU_metaplan`), the bus-emission correctness
hypothesis `h_bus_execute_matches_sail` is parameterized — D3e
DEFERRED shape (d) (memory-bus-read) inherits to LHU.
-/

namespace ZiskFv.Equivalence.LoadHU

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD
open ZiskFv.Spec.LoadHU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LHU theorem.** With the LD-shape load hypotheses
    plus the memory-bus entry's high 6 byte lanes zeroed (the `ind_width
    = 2` bus-side zero-pad), the Main row's packed `c` cell encodes the
    16-bit loaded value (equal to `memory_entry_half entry`).

    LHU-analogue of `equiv_LWU`, narrowed via `load_hu_compositional`. -/
theorem equiv_LHU
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : load_hu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_half entry :=
  load_hu_compositional m r_main next_pc entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LHU (`.LOAD (imm, rs1, rd, true, 2)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADHU_pure`,
    given the register/PC/memory/alignment assumptions.

    Wraps `PureSpec.execute_LOADHU_pure_equiv`, which delegates to the
    trusted `execute_LOADHU_pure_equiv_axiom` (sibling of M1/M3; see
    `RV64D/lhu.lean`). -/
theorem equiv_LHU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lhu_state_assumptions lhu_input state) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state
      = let output := PureSpec.execute_LOADHU_pure lhu_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADHU_pure_equiv
    lhu_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** The metaplan-target shape for RV64 LHU: Sail's
    `execute_instruction` on an LHU equals the state computed by applying
    `bus_effect` to the circuit's execution + memory bus rows.

    Composes `equiv_LHU_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_LWU_metaplan` /
    `equiv_LD_metaplan`, the bus-emission-correctness obligation is
    parameterized; D3e DEFERRED shape (d) (memory-bus-read) — LHU
    inherits the parameterization. -/
theorem equiv_LHU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lhu_state_assumptions lhu_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADHU_pure lhu_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             match output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LHU_sail state lhu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.LoadHU
