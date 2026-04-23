import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadWord
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.lw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LW (load word, signed / sign-extended).
Phase 3C T-SL0 — pilot of the `SignExtendLoadArchetype`. Consumes
`PureSpec.execute_LOADW_pure_equiv` directly (C9 retired by Phase 4
T-LW; also fixed a Phase 3B statement bug that passed
`is_unsigned = true` — correct for RV64 LW is `false`).

Parallels the Phase 3A LHU / LBU equivalence structure (same trio
of theorems) but consumes the signed-load archetype's bus-zeroing
corollary rather than LHU/LBU's memory-bus copy argument. The
`h_bus_execute_matches_sail` bus-matching hypothesis is
parameterized as in LHU / LBU / SLLW.
-/

namespace ZiskFv.Equivalence.Lw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.LoadWord

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LW theorem.** With the LW-shape Main constraints
    (`is_external_op = 1`, `op = OP_SIGNEXTEND_W`, `m32 = 1`, `flag = 0`,
    `set_pc = 0`) plus a bus-match to a secondary entry, the entry
    carries zeroed high `a` / `b` lanes: `a_hi = 0 ∧ b_hi = 0`. The
    32-bit source operand is conveyed via the low lanes; the
    BinaryExtension SM is responsible for the sign-extension
    computation which feeds back via the bus's `c` lanes. -/
theorem equiv_LW
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : lw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  lw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LW-shape LOAD reduces to the pure-function block supplied by
    `PureSpec.execute_LOADW_pure`, given the standard register/PC/memory
    assumptions. -/
theorem equiv_LW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lw_state_assumptions lw_input state) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state
      = let output := PureSpec.execute_LOADW_pure lw_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADW_pure_equiv (state := state)
    (mstatus := mstatus) (pmaRegion := pmaRegion) (misa := misa)
    (mseccfg := mseccfg) lw_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 LW
    (Phase 3B's LOAD-with-`(true, 4)` shape) equals the state computed
    by applying `bus_effect` to the circuit's execution + memory bus
    rows. Composes `equiv_LW_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail` (Phase-4-deferred bus-emission
    derivation, same shape as LHU / LBU / SLLW). -/
theorem equiv_LW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lw_state_assumptions lw_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADW_pure lw_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             match output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LW_sail state lw_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Lw
